`default_nettype none

module cache (
    // Global clock.
    input  wire        i_clk,
    // Synchronous active-high reset.
    input  wire        i_rst,
    // External memory interface. See hart interface for details. This
    // interface is nearly identical to the phase 5 memory interface, with the
    // exception that the byte mask (`o_mem_mask`) has been removed. This is
    // no longer needed as the cache will only access the memory at word
    // granularity, and implement masking internally.
    input  wire        i_mem_ready,
    output wire [31:0] o_mem_addr,
    output wire        o_mem_ren,
    output wire        o_mem_wen,
    output wire [31:0] o_mem_wdata,
    input  wire [31:0] i_mem_rdata,
    input  wire        i_mem_valid,

    // Interface to CPU hart. This is nearly identical to the phase 5 hart memory
    // interface, but includes a stall signal (`o_busy`), and the input/output
    // polarities are swapped for obvious reasons.
    //
    // The CPU should use this as a stall signal for both instruction fetch
    // (IF) and memory (MEM) stages, from the instruction or data cache
    // respectively. If a memory request is made (`i_req_ren` for instruction
    // cache, or either `i_req_ren` or `i_req_wen` for data cache), this
    // should be asserted *combinationally* if the request results in a cache
    // miss.
    //
    // In case of a cache miss, the CPU must stall the respective pipeline
    // stage and deassert ren/wen on subsequent cycles, until the cache
    // deasserts `o_busy` to indicate it has serviced the cache miss. However,
    // the CPU must keep the other request lines constant. For example, the
    // CPU should not change the request address while stalling.
    output wire        o_busy,
    // 32-bit read/write address to access from the cache. This should be
    // 32-bit aligned (i.e. the two LSBs should be zero). See `i_req_mask` for
    // how to perform half-word and byte accesses to unaligned addresses.
    input  wire [31:0] i_req_addr,
    // When asserted, the cache should perform a read at the aligned address
    // specified by `i_req_addr` and return the 32-bit word at that address,
    // either immediately (i.e. combinationally) on a cache hit, or
    // synchronously on a cache miss. It is illegal to assert this and
    // `i_dmem_wen` on the same cycle.
    input  wire        i_req_ren,
    // When asserted, the cache should perform a write at the aligned address
    // specified by `i_req_addr` with the 32-bit word provided in
    // `o_req_wdata` (specified by the mask). This is necessarily synchronous,
    // but may either happen on the next clock edge (on a cache hit) or after
    // multiple cycles of latency (cache miss). As the cache is write-through
    // and write-allocate, writes must be applied to both the cache and
    // underlying memory.
    // It is illegal to assert this and `i_dmem_ren` on the same cycle.
    input  wire        i_req_wen,
    // The memory interface expects word (32 bit) aligned addresses. However,
    // WISC-25 supports byte and half-word loads and stores at unaligned and
    // 16-bit aligned addresses, respectively. To support this, the access
    // mask specifies which bytes within the 32-bit word are actually read
    // from or written to memory.
    input  wire [ 3:0] i_req_mask,
    // The 32-bit word to write to memory, if the request is a write
    // (i_req_wen is asserted). Only the bytes corresponding to set bits in
    // the mask should be written into the cache (and to backing memory).
    input  wire [31:0] i_req_wdata,
    // THe 32-bit data word read from memory on a read request.
    output wire [31:0] o_res_rdata
);
  // These parameters are equivalent to those provided in the project
  // 6 specification. Feel free to use them, but hardcoding these numbers
  // rather than using the localparams is also permitted, as long as the
  // same values are used (and consistent with the project specification).
  //
  // 32 sets * 2 ways per set * 16 bytes per way = 1K cache
  localparam O = 4;  // 4 bit offset => 16 byte cache line
  localparam S = 5;  // 5 bit set index => 32 sets
  localparam DEPTH = 2 ** S;  // 32 sets
  localparam W = 2;  // 2 way set associative, NMRU
  localparam T = 32 - O - S;  // 23 bit tag
  localparam D = 2 ** O / 4;  // 16 bytes per line / 4 bytes per word = 4 words per line

  //reg versions of the outputs of the module 
  reg [31:0] o_mem_addr_reg;
  //assign o_mem_addr = o_mem_addr_reg;
  reg o_mem_ren_reg;
  //  assign o_mem_ren = o_mem_ren_reg;
  reg o_mem_wen_reg;
  reg [31:0] o_mem_wdata_reg;
  //assign o_mem_wdata = o_mem_wdata_reg;
  reg busy1;
  assign o_busy = busy1;

  // The following memory arrays model the cache structure. As this is
  // an internal implementation detail, you are *free* to modify these
  // arrays as you please.

  // Backing memory, modeled as two separate ways.
  reg [   31:0] datas0[DEPTH - 1:0][D - 1:0];   //stores first line in set   (32 lines x 4 words per line)
  reg [31:0] datas1[DEPTH - 1:0][D - 1:0];  //stores second line in set 
  reg [T - 1:0] tags0[DEPTH - 1:0];  //stores tag from first line in set
  reg [T - 1:0] tags1[DEPTH - 1:0];  //stores tag from second line in set
  reg [1:0] valid[DEPTH - 1:0];  //2-bit valid (one for each line in set)
  reg lru[DEPTH - 1:0];  //bit to track lru

  // Fill in your implementation here.

  /*
 i_req_addr is word aligned so 2 LSBs are 0 
 */
  wire [22:0] req_tag = i_req_addr[31:9];  //top 23 bits are tag 
  wire [4:0] req_index = i_req_addr[8:4];  //5 set bits in address
  wire [1:0] req_wrdOffset = i_req_addr[3:2];  //2 bits for word offset for 16-byte blocks 
  wire hit;

  //check if valid bit is set & if tag matches request 
  wire Line0_hit = valid[req_index][0] && (tags0[req_index] == req_tag);
  wire Line1_hit = valid[req_index][1] && (tags1[req_index] == req_tag);
  assign hit = Line0_hit || Line1_hit;

  reg cache_Rhit;
  reg ready2write;

  //FSM STATES
  localparam IDLE = 3'b000;
  localparam MEMREAD = 3'b001;
  localparam MEMWRITE = 3'b010;
  localparam OUT_DATA = 3'b011;
  localparam STALL = 3'b111;

  reg [2:0] state;
  reg [2:0] next_state;
  reg [2:0] prev_state;

  //fsm state transition
  always @(posedge i_clk) begin
    if (i_rst) begin
      state <= IDLE;
      prev_state <= IDLE;
    end else begin
      state <= next_state;
      prev_state <= state;
    end
  end

  //Basic recap of cache organization
  //32 sets, 2 way associative with each block having 4 words
  //2 bits of the address are required to access each word, word aligned hence
  //add[3:2]
  //2 way associative implies that each set can hold 2 blocks of data
  //32 sets, hence 5 bits required to index this, or add[8:4]
  //rest of the bits are used for tag-inspection, given by [31:9]
  //
  //When a request is sent by the CPI via i_req_wen or i_req_ren, check if its
  //a hit: if hit, combinational read from the cache. 


  ///////////RESET LOGIC
  integer i, x;
  always @(posedge i_clk) begin
    if (i_rst) begin
      for (i = 0; i < 32; i = i + 1) begin
        valid[i] <= 2'd0;
        tags0[i] <= 23'd0;
        tags1[i] <= 23'd0;
        lru[i]   <= 1'd0;
        for (x = 0; x < 4; x = x + 1) begin
          datas0[i][x] <= 32'b0;
          datas1[i][x] <= 32'b0;
        end
      end
    end
  end

  reg [1:0] mem_add_read;
  //2 registers to keep track of what the request-signal type was
  reg i_req_wen_ff;
  reg i_req_ren_ff;

  //set which kind of request
  always @(posedge i_clk) begin
    if (i_rst) begin
      i_req_wen_ff <= 1'b0;
      i_req_ren_ff <= 1'b0;
    end else begin
      if (state == IDLE) begin
        i_req_wen_ff <= i_req_wen;
        i_req_ren_ff <= i_req_ren;
      end
    end
  end


  reg [31:0] Write_Buffer_data;
  reg [31:0] Write_Buffer_addr;
  reg WriteHit_reg;

  wire [31:0] mask32 =
    (i_req_mask == 4'b1111) ? 32'hFFFFFFFF :
    (i_req_mask == 4'b0011) ? 32'h0000FFFF :
    (i_req_mask == 4'b1100) ? 32'hFFFF0000 :
    (i_req_mask == 4'b0001) ? 32'h000000FF :
    (i_req_mask == 4'b0010) ? 32'h0000FF00 :
    (i_req_mask == 4'b0100) ? 32'h00FF0000 :
    (i_req_mask == 4'b1000) ? 32'hFF000000 :
                              32'h00000000;

  wire Update_buffer = WriteHit_reg & ready2write;//last request was write hit and current is write hit 
  wire [31:0] cache_word =
    Line0_hit ? datas0[req_index][req_wrdOffset] :
    Line1_hit ? datas1[req_index][req_wrdOffset] : 
    32'h0;
  wire [31:0] Data2Write = (cache_word & ~mask32) | (i_req_wdata & mask32); //this should setup data to write to cache and memory

  always @(posedge i_clk) begin
    if (i_rst) begin
      Write_Buffer_data <= 1'b0;
      Write_Buffer_addr <= 1'b0;
    end else begin
      if (Update_buffer) begin
        Write_Buffer_data <= Data2Write;
        Write_Buffer_addr <= i_req_addr;
      end
    end
  end

  always @(posedge i_clk) begin
    if (i_rst) begin
      WriteHit_reg <= 1'b0;
    end else begin
      WriteHit_reg <= ready2write;
    end
  end

  //LOGIC FOR FETCHING LINES FROM MEMORY IN MEMREAD STATE
  //if currently in the MEMREAD state, attempt to sequentially read addresses
  //for the block 
  //the data to load from memory via offset should be given by this
  wire [31:0] o_req_addr_offset;
  reg  [31:0] flopped_i_req;

  //cycle to include word wanted and the following three words
  assign o_req_addr_offset = i_req_addr + {28'b0, mem_add_read, 2'b0};

  assign o_mem_addr = (state==MEMREAD)? o_req_addr_offset:
                      (state==MEMWRITE)? flopped_i_req:
                      (state==IDLE & hit)? i_req_addr:
                       32'b0;
  assign o_mem_ren = (state == MEMREAD) ? 1'b1 : 1'b0;



  always @(posedge i_clk) begin
    if (i_rst) begin
      flopped_i_req <= 32'd0;
    end else begin
      flopped_i_req <= i_req_addr;
    end
  end

  //logic for loading 4 words of data on any read from memory
  reg [1:0] block_offset;
  always @(posedge i_clk) begin
    if (i_rst || state == IDLE) begin
      block_offset <= 2'b0;
      mem_add_read <= 2'b0;
    end
    //if in any state other than MEMREAD, set mem_add_read to 0
    if (state == MEMREAD) begin
      if (~i_mem_ready) begin
        mem_add_read  <= mem_add_read;
        o_mem_ren_reg <= 1'b0;
      end else begin
        mem_add_read  <= mem_add_read + 1;
        o_mem_ren_reg <= 1'b1;
      end

      if (i_mem_valid) begin
        block_offset <= block_offset + 1;
        if (~valid[req_index][0]) begin
          datas0[req_index][block_offset] <= i_mem_rdata;
          tags0[req_index] <= req_tag;
          if (block_offset == 2'd3) begin
            valid[req_index][0] <= 1'b1;
            lru[req_index] <= 1'b1;  //way 0 was just used, so way 1 is LRU
          end
          //second line is empty
        end else if (~valid[req_index][1]) begin
          datas1[req_index][block_offset] <= i_mem_rdata;
          tags1[req_index] <= req_tag;
          if (block_offset == 2'd3) begin
            valid[req_index][1] <= 1'b1;
            lru[req_index] <= 1'b0;  //way 1 was just used, so way 0 is LRU
          end
          //neither are empty, evict lru
        end else begin
          if (lru[req_index] == 1'b0) begin
            datas0[req_index][block_offset] <= i_mem_rdata;
            tags0[req_index] <= req_tag;
            if (block_offset == 2'd3) begin
              lru[req_index] <= 1'b1;  //way 0 was just used, so way 1 is LRU
            end
          end else begin
            datas1[req_index][block_offset] <= i_mem_rdata;
            tags1[req_index] <= req_tag;
            if (block_offset == 2'd3) begin
              lru[req_index] <= 1'b0;  //way 1 was just used, so way 0 is LRU
            end
          end
        end
      end
    end
  end


  //TODO: masked data
  //on reads, data outputted by the cache to the CPU needs to be masked by the
  //provided mask
  wire[31:0] Cache_masked_output_val; //assigned straight from cache used for hits (used for read request)

  //set mask depending on recieved input 
  assign Cache_masked_output_val = cache_word & mask32;   // set final data to output on cache hit                     

  assign o_res_rdata = (cache_Rhit) ? Cache_masked_output_val : 32'b0;

  /*Logic for when in MemWrite stage */
  // when in MemWrite correct block is already in cache 
  // manipulate data 
  // write to cache 
  // write to memory 
  // reg [31:0] i_req_wdata_reg; 

  // always @(posedge i_clk) begin
  //   if(i_rst)begin 
  //     i_req_wdata_reg <= 32'd0; 
  //   end else if (state == IDLE)begin 
  //     i_req_wdata_reg <= i_req_wdata;
  //   end 
  // end 


  /*reg [31:0] mask32_reg;

  always @(posedge i_clk) begin
    if(i_rst)begin 
      mask32_reg <= 32'hFFFFFFFF; 
    end else begin 
      mask32_reg <= mask32;
    end 
  end 
*/



  always @(posedge i_clk) begin


    if (ready2write) begin
      if (Line0_hit) begin
        datas0[req_index][req_wrdOffset] <= Data2Write;
        lru[req_index] <= 1'b1;  //way 0 just used so way1 is LRU
      end

      if (Line1_hit) begin
        datas1[req_index][req_wrdOffset] <= Data2Write;
        lru[req_index] <= 1'b0;  //way 1 just used so way0 is LRU
      end

      //o_mem_wdata_reg <= Data2Write;
      //o_mem_wen_reg   <= 1'b1; 
      //o_mem_addr_reg  <= i_req_addr; 
    end
  end

  assign o_mem_wen   = ready2write;
  assign o_mem_wdata = Data2Write;

  //write signal to be set to 1 inside the state machine when in the write
  //state
  always @(*) begin
    //default values
    next_state = state;
    busy1 = 1'b0;
    cache_Rhit = 1'b0;
    ready2write = 1'b0;

    case (state)
      IDLE: begin

        cache_Rhit = 1'b1;
        if ((i_req_wen || i_req_ren) && ~hit) begin  //cache miss
          next_state = MEMREAD;
          //busy1 = 1'b1;
          cache_Rhit = 1'b0;
        end

        if (i_req_ren & hit) begin  //cache read hit 
          cache_Rhit = 1'b1;
        end

        if (hit && i_req_wen) begin  //cache write hit 
          cache_Rhit  = 1'b0;
          ready2write = 1'b1;
        end

      end
      MEMREAD: begin
        busy1 = 1'b1;  //stay busy while reading from memory 

        if (block_offset == 3'd3) begin  //after bringing in block we can leave this state 
          if (i_req_ren_ff && i_mem_valid) begin
            cache_Rhit = 1'b1;  //data from mem read is ready in cache
            next_state = OUT_DATA;
          end else if (i_req_wen_ff && i_mem_valid) begin
            next_state = MEMWRITE;
          end
        end
      end

      OUT_DATA: begin
        busy1 = 1'b1;
        cache_Rhit = 1'b1;
        next_state = IDLE;
      end

      MEMWRITE: begin //once we hit this state we can assume block is cache (next update word based on mask and input data)
        //if its a hit, busy1=0
        busy1 = 1'b1;  //hold busy to keep inputs stable 
        // if((Line0_hit || Line1_hit) && i_mem_ready & (prev_state != MEMWRITE))begin
        //   busy1=1'b0;
        // end
        if (i_mem_ready) begin
          ready2write = 1'b1;
          next_state  = STALL;
        end
      end

      STALL: begin
        busy1 = 1'b1;
        next_state = IDLE;  //stall here while mem becomes ready after last request issued 
      end

    endcase
  end

endmodule

`default_nettype wire

