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
  assign o_mem_addr = o_mem_addr_reg;
  reg o_mem_ren_reg;
  assign o_mem_ren = o_mem_ren_reg;
  reg o_mem_wen_reg;
  assign o_mem_wen = o_mem_wen_reg;
  reg [31:0] o_mem_wdata_reg;
  assign o_mem_wdata = o_mem_wdata_reg;
  reg busy1;
  assign o_busy = busy1;

  // The following memory arrays model the cache structure. As this is
  // an internal implementation detail, you are *free* to modify these
  // arrays as you please.

  // Backing memory, modeled as two separate ways.
  reg [   31:0] datas0[DEPTH - 1:0][D - 1:0];   //stores first line in set   (32 lines x 4 words per line)
  reg [   31:0] datas1[DEPTH - 1:0][D - 1:0];  //stores second line in set 
  reg [T - 1:0] tags0[DEPTH - 1:0];  //stores tag from first line in set
  reg [T - 1:0] tags1[DEPTH - 1:0];  //stores tag from second line in set
  reg [1:0] valid [DEPTH - 1:0];  //2-bit valid (one for each line in set)
  reg       lru   [DEPTH - 1:0];  //bit to track lru

  // Fill in your implementation here.

  /*
 i_req_addr is word aligned so 2 LSBs are 0 
 */
  wire [22:0] req_tag = i_req_addr[31:9];  //top 23 bits are tag 
  wire [4:0] req_index = i_req_addr[8:4];  //5 set bits in address
  wire [1:0] req_wrdOffset = i_req_addr[3:2];  //2 bits for word offset for 16-byte blocks 
  wire hit;

  // Declare all sequential registers early
  reg cache_Rhit;
  reg ready2write; 
  reg [31:0] latched_rdata;  // Latch read data for reads that complete 
  reg line_just_filled;  // Track when a line has just been filled from memory
  reg [4:0] filled_index;  // Index of the line that was just filled
  reg [22:0] filled_tag;  // Tag of the line that was just filled
  reg [1:0] mem_add_read;
  reg i_req_wen_ff;
  reg i_req_ren_ff;
  reg [4:0] mem_read_count;  // Count how many words have been read (0-4)
  reg [31:0] miss_addr;
  
  // Declare all wires for address decoding
  wire [22:0] miss_tag = miss_addr[31:9];
  wire [4:0] miss_index = miss_addr[8:4];
  wire [1:0] miss_wrdOffset = miss_addr[3:2];

  //check if valid bit is set & if tag matches request 
  wire Line0_hit = valid[req_index][0] && (tags0[req_index] == req_tag);
  wire Line1_hit = valid[req_index][1] && (tags1[req_index] == req_tag);
  // Also consider lines that just filled in MEMREAD (they're not yet valid in next cycle)
  wire line_just_filled_match = line_just_filled && (filled_index == req_index) && (filled_tag == req_tag);
  assign hit = Line0_hit || Line1_hit || line_just_filled_match;

  localparam IDLE    = 2'b00;
  localparam MEMREAD = 2'b01;
  localparam MEMWRITE= 2'b10;
  reg [1:0] state;
  reg [1:0] next_state;
  
  // Read path wires - used in combinational logic
  // During MEMWRITE after a miss, read from the latched filled address (for both read and write misses)
  // Otherwise use current request address
  wire [4:0] read_index = (state == MEMWRITE && line_just_filled) ? filled_index : req_index;
  wire [1:0] read_offset = (state == MEMWRITE && line_just_filled) ? miss_wrdOffset : req_wrdOffset;
  wire [22:0] read_tag = (state == MEMWRITE && line_just_filled) ? filled_tag : req_tag;
  
  // Check hits against the address being read
  wire read_Line0_hit = valid[read_index][0] && (tags0[read_index] == read_tag);
  wire read_Line1_hit = valid[read_index][1] && (tags1[read_index] == read_tag);
  
  // Cache word read from selected way
  wire [31:0] cache_word =
    read_Line0_hit ? datas0[read_index][read_offset] :
    read_Line1_hit ? datas1[read_index][read_offset] : 
    32'h0;
  
  // Data to write (masked merge of old data and new write data)
  wire [31:0] mask32 =
    (i_req_mask == 4'b1111) ? 32'hFFFFFFFF :
    (i_req_mask == 4'b0011) ? 32'h0000FFFF :
    (i_req_mask == 4'b1100) ? 32'hFFFF0000 :
    (i_req_mask == 4'b0001) ? 32'h000000FF :
    (i_req_mask == 4'b0010) ? 32'h0000FF00 :
    (i_req_mask == 4'b0100) ? 32'h00FF0000 :
    (i_req_mask == 4'b1000) ? 32'hFF000000 :
                              32'h00000000;
  
  wire [31:0] Data2Write = (cache_word & ~mask32) | (i_req_wdata & mask32);
  
  // Determine which address/offset to use for the write
  // During MEMWRITE after a miss, use latched miss address; otherwise use current request
  wire [4:0] write_index = (state == MEMWRITE && line_just_filled) ? filled_index : req_index;
  wire [1:0] write_offset = (state == MEMWRITE && line_just_filled) ? miss_wrdOffset : req_wrdOffset;
  wire [31:0] write_addr = (state == MEMWRITE && line_just_filled) ? miss_addr : i_req_addr;  //fsm state transition
  always @(posedge i_clk) begin
    if (i_rst) begin
      state <= IDLE;
      o_mem_addr_reg <= 32'b0;
      o_mem_ren_reg <= 1'b0;
      o_mem_wen_reg <= 1'b0;
      o_mem_wdata_reg <= 32'b0;
      line_just_filled <= 1'b0;
      filled_index <= 5'b0;
      filled_tag <= 23'b0;
    end else begin
      state <= next_state;
      // Set line_just_filled when transitioning OUT of MEMREAD
      if (state == MEMREAD && next_state != MEMREAD) begin
        line_just_filled <= 1'b1;
        filled_index <= miss_index;
        filled_tag <= miss_tag;
      // Clear line_just_filled only after we transition back to IDLE from MEMWRITE
      // or if we're in IDLE and it's been set (one cycle pulse)
      end else if ((state == MEMWRITE && next_state == IDLE) || 
                   (state == IDLE && line_just_filled && (i_req_wen || i_req_ren))) begin
        // Consume the flag: clear it at end of this cycle
        line_just_filled <= 1'b0;
      end
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

  // All reg/wire declarations are now at the top of the module
  // These lines are now removed to avoid duplicates

  //set which kind of request
  always @(posedge i_clk) begin
    if (i_rst) begin
      i_req_wen_ff <= 1'b0;
      i_req_ren_ff <= 1'b0;
      mem_read_count <= 5'b0;
      miss_addr <= 32'b0;
    end else begin
      if (state == IDLE && (i_req_wen || i_req_ren)) begin
        i_req_wen_ff <= i_req_wen;
        i_req_ren_ff <= i_req_ren;
        mem_read_count <= 5'b0;
        miss_addr <= i_req_addr;  // Latch address at start of miss
      end else if (state == MEMREAD) begin
        if (i_mem_valid) begin
          mem_read_count <= mem_read_count + 1;
        end
      end
    end
  end

  //LOGIC FOR FETCHING LINES FROM MEMORY IN MEMREAD STATE
  //if currently in the MEMREAD state, attempt to sequentially read addresses
  //for the block 
  //the data to load from memory via offset should be given by this
  wire [31:0] line_aligned_addr;  // Address aligned to start of cache line
  wire [31:0] o_req_addr_offset;

  // Align address to cache line boundary (zero out lower 4 bits which are offset into line)
  // Use the latched miss address during MEMREAD, else use current address
  wire [31:0] addr_for_fetch = (state == MEMREAD) ? miss_addr : i_req_addr;
  assign line_aligned_addr = {addr_for_fetch[31:4], 4'b0000};
  
  //cycle to include word wanted and the following three words
  assign o_req_addr_offset = line_aligned_addr + {28'b0, mem_add_read, 2'b0};
  
  //logic for loading 4 words of data on any read from memory
  always @(posedge i_clk) begin
    if (i_rst) begin
      mem_add_read <= 2'b0;
      o_mem_ren_reg <= 1'b0;
    end else if (state != MEMREAD) begin
      //if in any state other than MEMREAD, set mem_add_read to 0
      mem_add_read <= 2'b0;
      o_mem_ren_reg <= 1'b0;
    end else if (state == MEMREAD) begin
      if (i_mem_ready) begin
        o_mem_addr_reg <= o_req_addr_offset;
        o_mem_ren_reg <= 1'b1;
      end else begin
        o_mem_ren_reg <= 1'b0;
      end 

      if (i_mem_valid) begin
        if (~valid[miss_index][0]) begin
          datas0[miss_index][mem_add_read] <= i_mem_rdata;
          if (mem_add_read == 2'd3) begin
            tags0[miss_index] <= miss_tag;
            valid[miss_index][0] <= 1'b1;
            lru[miss_index] <= 1'b1;
          end else begin
            tags0[miss_index] <= miss_tag;
          end
        end else if (~valid[miss_index][1]) begin
          datas1[miss_index][mem_add_read] <= i_mem_rdata;
          if (mem_add_read == 2'd3) begin
            tags1[miss_index] <= miss_tag;
            valid[miss_index][1] <= 1'b1;
            lru[miss_index] <= 1'b0;
          end else begin
            tags1[miss_index] <= miss_tag;
          end
        end else begin
          if (lru[miss_index] == 1'b0) begin
            datas0[miss_index][mem_add_read] <= i_mem_rdata;
            if (mem_add_read == 2'd3) begin
              tags0[miss_index] <= miss_tag;
              lru[miss_index] <= 1'b1;
            end else begin
              tags0[miss_index] <= miss_tag;
            end
          end else begin
            datas1[miss_index][mem_add_read] <= i_mem_rdata;
            if (mem_add_read == 2'd3) begin
              tags1[miss_index] <= miss_tag;
              lru[miss_index] <= 1'b0;
            end else begin
              tags1[miss_index] <= miss_tag;
            end
          end
        end
        mem_add_read <= mem_add_read + 1;
      end
    end
  end


  //TODO: masked data
  //on reads, data outputted by the cache to the CPU needs to be masked by the
  //provided mask
   wire[31:0] Cache_masked_output_val; //assigned straight from cache used for hits (used for read request)

  assign Cache_masked_output_val = cache_word & mask32;   // set final data to output on cache hit                     

  assign o_res_rdata = Cache_masked_output_val; 

 /*Logic for when in MemWrite stage */
 // when in MemWrite correct block is already in cache 
 // manipulate data 
 // write to cache 
 // write to memory 

 // Note: Data2Write, read_Line0_hit, read_Line1_hit, write_index, write_offset, write_addr already declared above

 always @(posedge i_clk) begin

  if (i_rst) begin
    o_mem_wen_reg <= 1'b0;
  end else if(state == MEMWRITE && ready2write && (read_Line0_hit || read_Line1_hit)) begin 
      // Only write when we have a hit (data is in cache)
      if(read_Line0_hit)begin
        datas0[write_index][write_offset] <= Data2Write;
        lru[write_index] <= 1'b1; //way 0 just used so way1 is LRU
      end 

      if(read_Line1_hit)begin 
        datas1[write_index][write_offset] <= Data2Write;
        lru[write_index] <= 1'b0; //way 1 just used so way0 is LRU
      end 

      o_mem_wdata_reg <= Data2Write;
      o_mem_wen_reg   <= 1'b1; 
      o_mem_addr_reg  <= write_addr; 

  end else begin
    o_mem_wen_reg <= 1'b0;
  end
 end 




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
         
        if ((i_req_wen || i_req_ren) && ~hit) begin //cache miss
          next_state = MEMREAD;
          busy1 = 1'b1;
        end else if (i_req_ren && hit) begin    //cache read hit 
          cache_Rhit = 1'b1;
          busy1 = 1'b0;
        end else if (i_req_wen && hit) begin //cache write hit 
          next_state = MEMWRITE;
          busy1 = 1'b1;
        end

      end
      MEMREAD: begin

        busy1 = 1'b1; //stay busy while reading from memory 

        if (mem_read_count == 5'd4) begin //after bringing in all 4 words we can leave this state 
          if (i_req_ren_ff) begin
            cache_Rhit = 1'b1;    //data from mem read is ready in cache
            next_state = IDLE;
            busy1 = 1'b0;
          end else if (i_req_wen_ff) begin
            next_state = MEMWRITE;
            busy1 = 1'b1;
          end
        end
      end

      MEMWRITE: begin //once we hit this state we can assume block is cache (next update word based on mask and input data)
        busy1 = 1'b1;  //hold busy to keep inputs stable 
        ready2write = 1'b1;
        if(i_mem_ready)begin 
          next_state = IDLE;
          busy1 = 1'b0;
        end 
      end

    endcase
  end

endmodule

`default_nettype wire

