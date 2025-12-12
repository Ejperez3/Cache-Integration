`default_nettype none
//TODO: need to modify hart to implement the logic of
//
//input signal that indicates that the memory is ready to take another request
//i_imem_ready
//
//output signal that indicates that sends a request signal to the instruction
//memory
//o_imem_ren
//
// input signal that indicates that the current instruction shown by memory to
// the CPU is valid
//i_imem_valid
//
//
//input signal indicating that the memory data/cache is ready to take
//a request
//i_dmem_ready
//
//
//input signal that indicates that the retrieved data from memory is valid
//i_dmem_valid
//
/////////////////////////////////////////////////////////////////////////////
////////////////// How it should work ///////////////////////////////////////
//
///////////////////Data Memory///////////////////
//- if i_dmem_ready is true (i.e, memoryc can take a request) and o_dmem_ren
//or o_dmem_wen is true, then send the request. 
//- if i_dmem_ready is FALSE (memory is busy) and o_dmem_ren or o_dmem_wen is
//true, then STALL?
//
///////////////////Instruction Memory//////////
// To be done later, idk bruh

module hart #(
    // After reset, the program counter (PC) should be initialized to this
    // address and start executing instructions from there.
    parameter RESET_ADDR = 32'h00000000
) (
    // Global clock.
    input  wire        i_clk,
    // Synchronous active-high reset.
    input  wire        i_rst,
    // Instruction fetch goes through a read only instruction memory (imem)
    // port. The port accepts a 32-bit address (e.g. from the program counter)
    // per cycle and combinationally returns a 32-bit instruction word. This
    // is not representative of a realistic memory interface; it has been
    // modeled as more similar to a DFF or SRAM to simplify phase 3. In
    // later phases, you will replace this with a more realistic memory.
    //
    // 32-bit read address for the instruction memory. This is expected to be
    // 4 byte aligned - that is, the two LSBs should be zero.
    input  wire        i_imem_ready,
    output wire [31:0] o_imem_raddr,
    output wire        o_imem_ren,
    // Instruction word fetched from memory, available on the same cycle.
    input  wire        i_imem_valid,
    input  wire [31:0] i_imem_rdata,
    // Data memory accesses go through a separate read/write data memory (dmem)
    // that is shared between read (load) and write (stored). The port accepts
    // a 32-bit address, read or write enable, and mask (explained below) each
    // cycle. Reads are combinational - values are available immediately after
    // updating the address and asserting read enable. Writes occur on (and
    // are visible at) the next clock edge.
    //
    // Read/write address for the data memory. This should be 32-bit aligned
    // (i.e. the two LSB should be zero). See `o_dmem_mask` for how to perform
    // half-word and byte accesses at unaligned addresses.
    input  wire        i_dmem_ready,
    output wire [31:0] o_dmem_addr,
    // When asserted, the memory will perform a read at the aligned address
    // specified by `i_addr` and return the 32-bit word at that address
    // immediately (i.e. combinationally). It is illegal to assert this and
    // `o_dmem_wen` on the same cycle.
    output wire        o_dmem_ren,
    // When asserted, the memory will perform a write to the aligned address
    // `o_dmem_addr`. When asserted, the memory will write the bytes in
    // `o_dmem_wdata` (specified by the mask) to memory at the specified
    // address on the next rising clock edge. It is illegal to assert this and
    // `o_dmem_ren` on the same cycle.
    output wire        o_dmem_wen,
    // The 32-bit word to write to memory when `o_dmem_wen` is asserted. When
    // write enable is asserted, the byte lanes specified by the mask will be
    // written to the memory word at the aligned address at the next rising
    // clock edge. The other byte lanes of the word will be unaffected.
    output wire [31:0] o_dmem_wdata,
    // The dmem interface expects word (32 bit) aligned addresses. However,
    // WISC-25 supports byte and half-word loads and stores at unaligned and
    // 16-bit aligned addresses, respectively. To support this, the access
    // mask specifies which bytes within the 32-bit word are actually read
    // from or written to memory.
    //
    // To perform a half-word read at address 0x00001002, align `o_dmem_addr`
    // to 0x00001000, assert `o_dmem_ren`, and set the mask to 0b1100 to
    // indicate that only the upper two bytes should be read. Only the upper
    // two bytes of `i_dmem_rdata` can be assumed to have valid data; to
    // calculate the final value of the `lh[u]` instruction, shift the rdata
    // word right by 16 bits and sign/zero extend as appropriate.
    //
    // To perform a byte write at address 0x00002003, align `o_dmem_addr` to
    // `0x00002003`, assert `o_dmem_wen`, and set the mask to 0b1000 to
    // indicate that only the upper byte should be written. On the next clock
    // cycle, the upper byte of `o_dmem_wdata` will be written to memory, with
    // the other three bytes of the aligned word unaffected. Remember to shift
    // the value of the `sb` instruction left by 24 bits to place it in the
    // appropriate byte lane.
    output wire [ 3:0] o_dmem_mask,
    // The 32-bit word read from data memory. When `o_dmem_ren` is asserted,
    // this will immediately reflect the contents of memory at the specified
    // address, for the bytes enabled by the mask. When read enable is not
    // asserted, or for bytes not set in the mask, the value is undefined.
    input  wire        i_dmem_valid,
    input  wire [31:0] i_dmem_rdata,
    // The output `retire` interface is used to signal to the testbench that
    // the CPU has completed and retired an instruction. A single cycle
    // implementation will assert this every cycle; however, a pipelined
    // implementation that needs to stall (due to internal hazards or waiting
    // on memory accesses) will not assert the signal on cycles where the
    // instruction in the writeback stage is not retiring.
    //
    // Asserted when an instruction is being retired this cycle. If this is
    // not asserted, the other retire signals are ignored and may be left invalid.
    output wire        o_retire_valid,
    // The 32 bit instruction word of the instrution being retired. This
    // should be the unmodified instruction word fetched from instruction
    // memory.
    output wire [31:0] o_retire_inst,
    // Asserted if the instruction produced a trap, due to an illegal
    // instruction, unaligned data memory access, or unaligned instruction
    // address on a taken branch or jump.
    output wire        o_retire_trap,
    // Asserted if the instruction is an `ebreak` instruction used to halt the
    // processor. This is used for debugging and testing purposes to end
    // a program.
    output wire        o_retire_halt,
    // The first register address read by the instruction being retired. If
    // the instruction does not read from a register (like `lui`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs1_raddr,
    // The second register address read by the instruction being retired. If
    // the instruction does not read from a second register (like `addi`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs2_raddr,
    // The first source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs1 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs1_rdata,
    // The second source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs2 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs2_rdata,
    // The destination register address written by the instruction being
    // retired. If the instruction does not write to a register (like `sw`),
    // this should be 5'd0.
    output wire [ 4:0] o_retire_rd_waddr,
    // The destination register data written to the register file in the
    // writeback stage by this instruction. If rd is 5'd0, this field is
    // ignored and can be treated as a don't care.
    output wire [31:0] o_retire_rd_wdata,
    output wire [31:0] o_retire_dmem_addr,
    output wire [ 3:0] o_retire_dmem_mask,
    output wire        o_retire_dmem_ren,
    output wire        o_retire_dmem_wen,
    output wire [31:0] o_retire_dmem_rdata,
    output wire [31:0] o_retire_dmem_wdata,
    // The current program counter of the instruction being retired - i.e.
    // the instruction memory address that the instruction was fetched from.
    output wire [31:0] o_retire_pc,
    // the next program counter after the instruction is retired. For most
    // instructions, this is `o_retire_pc + 4`, but must be the branch or jump
    // target for *taken* branches and jumps.
    output wire [31:0] o_retire_next_pc

`ifdef RISCV_FORMAL
    ,`RVFI_OUTPUTS,
`endif
);

  /*
Delcleration of any extra wires needed for connecting modules and for signals used across modules 
*/

  wire [31:0] JB_PC;
  wire [31:0] next_PC;  //holds the adress to be updated in PC next 
  wire [31:0] PC_plus4;  //will hold PC+4 value

  wire        jal_C;  //control signal 
  wire        jalr_C;  //control signal 
  wire        branch_C;  //control signal 
  wire        MemRead_C;  //control signal 
  wire        MemWrite_C;  //control signal 
  wire [ 1:0] Data_sel_C;  //control signal 
  wire [ 2:0] ALUop_C;  //control signal 
  wire [31:0] ALU_operand1;  //alu operand 1
  wire [31:0] ALU_operand2;  //alu operand 2
  wire [31:0] immediate_val;  //generated immeidate 
  wire [31:0] Mem_WD;  //feeds into memory write data port 
  wire [ 2:0] func3_val;  //feeds into branch logic block
  wire [ 3:0] func_val;  //feeds into ALU control block

  wire [31:0] ALU_result;  //ALU operation result
  wire [ 1:0] PC_MUX_SEL;  //MUX select signal for choosing next PC
  wire [31:0] PC_offset;  //PC + immediate offset value
  wire [31:0] MEM_DATA;  //Data returned from memory read  
  wire [31:0] WB_DATA;  //data to be input into register file 
  wire IF_ID_En;  

  reg reg2_regWrite;
  reg [31:0] reg3_curr_instruct;

  /* 
 Instantiate IF section of proccesor 
*/

//signal indicating that the memory is ready to take another request
//MEMORY STALL SIGNALS
  // choose between PC+4 or jump/Branch PC (By default should be PC+4)
  reg rst_reg;

  wire i_cache_stall;
  wire d_cache_stall;
  wire PC_En;
  assign next_PC =(rst_reg)?(32'd0):((~IF_ID_En||i_cache_stall||d_cache_stall)?(PC_plus4-32'd4):((PC_MUX_SEL[0]) ? JB_PC : PC_plus4));

  wire[31:0] current_PC_w;
  IF fetch_inst (
      .IF_EN(IF_ID_En),
      .i_clk   (i_clk),   //input- clk to control PC update
      .i_rst   (i_rst),   //input- used to reset PC to starting value
      .i_NextPC(next_PC), //input- next PC value                           

      .o_PC(current_PC_w),            //output- current PC feed into instruction memory and other locations (schematic) 
      .o_inc_pc(PC_plus4)  //output- current PC + 4 
  );
  wire[31:0] raw_current_PC;
  wire flush;
  reg flopped_flush;
  //should account for flused jump logic
  assign raw_current_PC=(flush)?next_PC:
    (flopped_flush)?next_PC:
    (IF_ID_En)?(current_PC_w):
                        (current_PC_w==32'b0)?(current_PC_w):
                        (current_PC_w-32'd4);

  //NEED TO USE A POST FLOPPED THING
  reg[31:0] current_PC;
  always@(posedge i_clk)begin
    if(i_rst)begin
      current_PC<=32'b0;
    flopped_flush<=1'b0;
  end
  else begin
      if(flush)
        flopped_flush<=1'b1;
      else
        flopped_flush<=1'b0;
  current_PC<=raw_current_PC;
  end
  end

  wire Mux_sel;
wire i_cache_req_ren;
  wire [31:0] i_cache_instruct;
  cache I_cache(
    .i_clk(i_clk),
    .i_rst(i_rst),
    .i_mem_ready(i_imem_ready),
    .o_mem_addr(o_imem_raddr),
    .o_mem_ren(o_imem_ren),
    .o_mem_wen(),
    .o_mem_wdata(),
    .i_mem_rdata(i_imem_rdata),
    .i_mem_valid(i_imem_valid),
    .o_busy(i_cache_stall),
    .i_req_addr(current_PC),
    .i_req_ren(i_cache_req_ren),
    .i_req_wen(1'b0),
    .i_req_mask(4'b1111),
    .i_req_wdata(32'b0),
    .o_res_rdata(i_cache_instruct)
  );


  /* 
 IF/ID Piepline Register
 Include NOP control
 TODO: EXPECTS INPUT OF NOP comm
*/
wire m_cache_req_ren;
assign i_cache_req_ren=(i_rst)?1'b0:1'b1;
  always@(posedge i_clk)begin
    if(i_rst)
      rst_reg<=1'b1;
    else
      rst_reg<=1'b0;
  end


  wire branch_taken; 
  assign branch_taken = (PC_MUX_SEL == 2'b11);
  //TODO: 
  reg reg1_jal_C;
  reg reg0_jal_C;
  reg reg0_jalr_C;
  reg flopped_i_cache_stall;

  assign flush=(reg0_jal_C ||reg0_jalr_C||branch_taken);



  reg [31:0] reg0_PC_plus4;
  reg [31:0] reg0_current_PC;
  reg [31:0] reg0_curr_instruct;
  reg reg0_MemRead_C;
  reg reg0_retire_valid; 

  //only load in values into reg0_current_instruct if i_imem_valid
  always @(posedge i_clk) begin
    //if the instruction being shown is NOT valid, add a nop?
    if (i_rst || rst_reg||flush) begin
      reg0_PC_plus4      <= 32'd0;
      reg0_current_PC    <= 32'd0;
      reg0_curr_instruct <= 32'd0;
      reg0_retire_valid  <= 1'd0; 
      //you can load the instruction if its being shown as valid
    end else if (IF_ID_En) begin
      reg0_PC_plus4      <= PC_plus4;
      reg0_current_PC    <= current_PC;
      reg0_curr_instruct <= i_cache_instruct;
      reg0_retire_valid  <= 1'd1;
    end else begin
      reg0_PC_plus4      <= reg0_PC_plus4;
      reg0_current_PC    <= reg0_current_PC;
      reg0_curr_instruct <= reg0_curr_instruct;
      reg0_retire_valid  <= reg0_retire_valid; 
    end
  end
  wire [4:0] IF_ID_RS1;
  wire [4:0] IF_ID_RS2;

  //input
  wire [4:0] ID_EX_WriteReg;
  wire ID_EX_RegWrite;

  wire [4:0] EX_MEM_WriteReg;
  wire EX_MEM_RegWrite;
  reg reg0_regWrite;
  reg [31:0] reg1_curr_instruct;
  reg [31:0] reg2_curr_instruct;
  reg reg1_regWrite; 

  //output

  //NOTE: hazard should now stall 
  //always request instructions from memory?
  wire dmem_wen;
  hazard haz (
    .i_cache_stall(i_cache_stall),
      .op_code(reg0_curr_instruct[6:0]),
      .IF_ID_RS1(reg0_curr_instruct[19:15]),
      .IF_ID_RS2(reg0_curr_instruct[24:20]), 
      .ID_EX_WriteReg(reg1_curr_instruct[11:7]),
      .valid_inst(reg0_retire_valid),
      .ID_EX_MemRead(reg0_MemRead_C),
      .PC_En(PC_En),
      .IF_ID_En(IF_ID_En),
      .Mux_sel(Mux_sel)
  );

  /* 
 Instantiate ID section of proccesor 
*/

  //////////Internal Wires////////////
  //to connect top-level register file to decode block
  wire [31:0] regData1;
  wire [31:0] regData2;
  wire regWrite;
  wire ALUmux1;
  wire ALUmux2;

  ID decode_I (
    .ALUmux1(ALUmux1),
    .ALUmux2(ALUmux2),
      .rst        (i_rst),               //input- to RF
      .clk        (i_clk),               //input- to RF
      .i_instruct (reg0_curr_instruct),  //input- full instruction input
      .i_currentPC(reg0_current_PC),     //input- the current PC value (used for auipc instruction)
      .o_RegWrite (regWrite),
      .i_regData1 (regData1),
      .i_regData2 (regData2),
      .o_jal     (jal_C),          //output- from control unit
      .o_jalr    (jalr_C),         //output- from control unit
      .o_branch  (branch_C),       //output- from control unit
      .o_MemRead (MemRead_C),      //output- from control unit
      .o_Data_sel(Data_sel_C),     //output- from control unit used for WB module
      .o_MemWrite(MemWrite_C),     //output- from control unit
      .o_op1     (ALU_operand1),   //output- from control unit (select ALU operand)
      .o_op2     (ALU_operand2),   //output- from control unit (selects ALU operand)
      .o_ALUop   (ALUop_C),        //output- from control unit goes to ALU control
      .o_imm     (immediate_val),  //output- the generated immediate 
      .o_Rdata2  (Mem_WD),         //output- will feed into memory 'write data' port 
      .func      (func_val),       //output- combination of func7 and func3 for ALU control block
      .func3     (func3_val)       //output- func 3 for branch logic 
  );

  //write adress should be 0 when instruction does not write to register 
  wire [4:0] rf_writeAddress;
  assign rf_writeAddress = (reg2_regWrite) ? reg3_curr_instruct[11:7] : 5'b00000;

  wire [31:0] WriteDataReg;
  rf rf (
      .i_clk(i_clk),
      .i_rst(i_rst),

      .i_rs1_raddr(reg0_curr_instruct[19:15]),
      .i_rs2_raddr(reg0_curr_instruct[24:20]),

      .o_rs1_rdata(regData1),
      .o_rs2_rdata(regData2),

      .i_rd_waddr(rf_writeAddress),
      .i_rd_wen  (reg2_regWrite),
      .i_rd_wdata(WriteDataReg)
  );



/* 
 ID/EX Piepline Register
*/
  reg [31:0] reg1_PC_plus4;
  reg ALUmux1_reg0;
  reg ALUmux2_reg0;
  reg [31:0] reg1_current_PC;
  reg [31:0] reg0_immediate_val;
  reg [2:0] reg0_func3_val;
  reg reg0_branch_C;
  reg [1:0] reg0_Data_sel_C;
  reg reg0_MemWrite_C;
  reg [31:0] reg0_ALU_operand1;
  reg [31:0] reg0_ALU_operand2;
  reg [31:0] reg0_Mem_WD;
  reg [2:0] reg0_ALUop_C;
  reg [3:0] reg0_func_val;
  reg [6:0] reg0_OP;
  reg reg1_retire_valid; 


reg [31:0] reg0_regData1;
reg [31:0] reg0_regData2;
  //include mux to control WB, M and EX inputs 

  always @(posedge i_clk) begin
    if (i_rst || Mux_sel || flush) begin
      ALUmux1_reg0<=1'b0;
      ALUmux2_reg0<=1'b0;
      reg1_current_PC    <= 32'd0;
      reg1_PC_plus4      <= 32'd0;
      reg0_immediate_val <= 32'd0;
      reg0_func3_val     <= 3'd0;
      reg0_jal_C         <= 1'd0;
      reg0_jalr_C        <= 1'd0;
      reg0_branch_C      <= 1'd0;
      reg0_regWrite      <= 1'd0;
      reg0_MemRead_C     <= 1'd0; 
      reg0_Data_sel_C    <= 2'd0; 
      reg0_MemWrite_C    <= 1'd0;
      reg0_ALU_operand1  <= 32'd0;
      reg0_ALU_operand2  <= 32'd0;
      reg0_Mem_WD        <= 32'd0;
      reg0_ALUop_C       <= 3'd0;
      reg0_func_val      <= 4'd0;
      reg0_OP            <= 7'd0;
      reg1_curr_instruct <= 32'd0;
      reg1_retire_valid  <= 1'd0;
      reg0_regData1      <= 32'd0;
      reg0_regData2      <=32'd0;

    end else if (~d_cache_stall) begin
      ALUmux1_reg0<=ALUmux1;
      ALUmux2_reg0<=ALUmux2;
      reg1_current_PC    <= reg0_current_PC;
      reg1_PC_plus4      <= reg0_PC_plus4;
      reg0_immediate_val <= immediate_val;
      reg0_func3_val     <= func3_val;
      reg0_jal_C         <= jal_C;
      reg0_jalr_C        <= jalr_C;
      reg0_branch_C      <= branch_C;
      reg0_regWrite      <= regWrite;
      reg0_MemRead_C     <= MemRead_C;
      reg0_Data_sel_C    <= Data_sel_C;
      reg0_MemWrite_C    <= MemWrite_C;
      reg0_ALU_operand1  <= ALU_operand1;
      reg0_ALU_operand2  <= ALU_operand2;
      reg0_Mem_WD        <= Mem_WD;
      reg0_ALUop_C       <= ALUop_C;
      reg0_func_val      <= func_val;
      reg0_OP            <= reg0_curr_instruct[6:0];
      reg1_curr_instruct <= reg0_curr_instruct; 
      reg1_retire_valid  <= reg0_retire_valid;
      reg0_regData1      <= regData1;
      reg0_regData2      <= regData2;      
    end 
 end





wire fw_mux1;
wire fw_mux2;

wire [31:0] fw_alu_op1;
wire [31:0] fw_alu_op2;
wire [31:0] ialu_operand1;
wire [31:0] ialu_operand2;
 wire fw3_mux_sel;
  reg [31:0] reg0_ALU_result;
  wire[31:0] forward_signal;
 Forwarding_unit fw1(
   .FW3_mux_sel(fw3_mux_sel),
   .op_code(reg1_curr_instruct[6:0]),
   .reg_enable_1(ALUmux1_reg0),
   .reg_enable_2(ALUmux2_reg0),

    //When the instruction reaches EX, it checks if its rs1 or rs2 register matches the rd register of any instruction ahead 
    //in the pipeline (EX/MEM or MEM/WB) If yes — we take that newer value instead of the stale one from the register file.

    .IDEX_RS1(reg1_curr_instruct[19:15]), //rs1 read reg in EX
    .IDEX_RS2(reg1_curr_instruct[24:20]), //rs2 read reg in eX

    .EXMEM_RD(reg2_curr_instruct[11:7]),   //future RD registers 
    .MEMWB_RD(reg3_curr_instruct[11:7]),

    .EXMEM_regWrite(reg1_regWrite), //Write enable signals 
    .MEMWB_regWrite(reg2_regWrite),

    .EXMEM_aluResult(forward_signal),
    .MEMWB_wbValue(WriteDataReg),

    .FW1_mux_sel(fw_mux1),
    .FW2_mux_sel(fw_mux2),
    .FW_data1(fw_alu_op1),
    .FW_data2(fw_alu_op2)
);

wire[31:0] sw_bypass;
wire[31:0] sw_retire_rs2;

assign sw_retire_rs2=(fw3_mux_sel)? sw_bypass:
                     (fw_mux2) ? ialu_operand2:
                      reg0_Mem_WD;

assign sw_bypass=(fw3_mux_sel)?(fw_alu_op2):(reg0_Mem_WD);



assign ialu_operand1 = (fw_mux1) ? fw_alu_op1 :reg0_ALU_operand1;
assign ialu_operand2 = (fw_mux2) ? fw_alu_op2 :reg0_ALU_operand2;

  /* 
 Instantiate EX section of proccesor 
*/
  EX execute_I (
      .i_pc(reg1_current_PC),      //input- Current PC input should be added to immediate (used for branch instructions)
      .func3(reg0_func3_val),  //input- func 3 input for branch logic block (branch.v file)
      .i_jal(reg0_jal_C),  //input- control signal for branch logic block
      .i_jalr(reg0_jalr_C),  //input- control signal for branch logic block
      .i_branch(reg0_branch_C),  //input- control signal for branch logic block
      .i_ALUOp(reg0_ALUop_C),  //input- input to ALU CTRL unit
      .i_op1(ialu_operand1),  //input- ALU operand1
      .i_op2(ialu_operand2),  //input- ALU operand2
      .i_imm(reg0_immediate_val),        //input- i_imm is used for adding to current PC if we are in I instruction i_op2 will be input as immediate already
      .func(reg0_func_val),  //input- combination of func7 and func 3 used by ALU control

      .o_result(ALU_result),  //output- ALU result
      .o_PC_Select(PC_MUX_SEL),     //output- MUX select signals from branch logic unit used to select next PC
      .o_inc_pc(PC_offset)          //output- The current PC + Immediate (used for branch adress calculation)
  );

  
assign JB_PC = (PC_MUX_SEL[1]) ? PC_offset :  ALU_result;

wire byte_hw_unsigned;
wire [3:0] mask;
wire [31:0] WriteDataMem;
reg [3:0]  reg1_mask;
reg reg1_byte_hw_unsigned;

S_extend dataEXT(
  .i_mask(mask),         
  .i_unsign(byte_hw_unsigned),
  .i_old_mask(reg1_mask),
  .i_old_unsign(reg1_byte_hw_unsigned), 

  .i_Rs2Data(sw_bypass),                 //register data input 
  .o_Memdata(WriteDataMem),           //aligned output based on mask 

  .i_WB(WB_DATA),
  .o_regData(WriteDataReg)
);


wire [31:0] aligned_address;
  mask_gen mask_gen (
      .address(ALU_result),
      .func3(reg0_func3_val),
      .aligned_address(aligned_address),
      .o_unsigned(byte_hw_unsigned),
      .mask(mask),
      .opcode(reg0_OP)
  );


  /*
  EX/MEM Pipeline Register
  */
  reg [31:0] reg2_PC_plus4;
  reg [31:0] reg0_aligned_address; 
  reg [3:0] reg0_mask;
  reg reg0_byte_hw_unsigned;
  reg [31:0] reg1_immediate_val; 
  reg reg1_MemRead_C;
  reg [1:0] reg1_Data_sel_C; 
  reg reg1_MemWrite_C; 
  reg [31:0] reg0_WriteDataMem; 
  reg reg2_retire_valid;
  reg [31:0] reg2_current_PC;

  reg [31:0] reg1_regData1;
  reg [31:0] reg1_regData2;

  always @(posedge i_clk) begin
    if (i_rst) begin
      reg1_jal_C<=1'b0;
      reg2_PC_plus4 <= 32'b0;
      reg0_aligned_address <= 32'b0;
      reg0_mask <= 4'b0;
      reg0_byte_hw_unsigned <= 1'b0;
      reg0_ALU_result <= 32'b0;
      reg1_immediate_val <= 32'd0;
      reg1_regWrite <= 1'd0;
      reg1_MemRead_C <= 1'd0;
      reg1_Data_sel_C <= 2'd0;
      reg1_MemWrite_C <= 1'd0;
      reg0_WriteDataMem <= 32'd0;
      reg2_curr_instruct <= 32'd0;
      reg2_retire_valid  <= 1'd0;
      reg2_current_PC    <= 32'd0;
      reg1_regData2     <= 32'd0;
      reg1_regData1     <= 32'd0;   

    end else if(~d_cache_stall) begin
      reg1_jal_C<=reg0_jal_C;
      reg2_PC_plus4 <= reg1_PC_plus4;
      reg0_aligned_address <= aligned_address;
      reg0_mask <= mask;
      reg0_byte_hw_unsigned <= byte_hw_unsigned;
      reg0_ALU_result <= ALU_result;
      reg1_immediate_val <= reg0_immediate_val;
      reg1_regWrite <= reg0_regWrite;
      reg1_MemRead_C <= reg0_MemRead_C;
      reg1_Data_sel_C <= reg0_Data_sel_C;
      reg1_MemWrite_C <= reg0_MemWrite_C;
      reg0_WriteDataMem <= WriteDataMem;
      reg2_curr_instruct <= reg1_curr_instruct;
      reg2_retire_valid  <= reg1_retire_valid;
      reg2_current_PC    <= reg1_current_PC;
      reg1_regData2     <= sw_retire_rs2;
      reg1_regData1     <= ialu_operand1;       
    end
  end

  /* 
 Instantiate MEM section of proccesor  (actual memory access done outside MEM module)
*/
  assign forward_signal=
    (reg1_Data_sel_C==2'b00)?reg2_PC_plus4:
    (reg1_Data_sel_C==2'b01)?reg1_immediate_val:
    (reg1_Data_sel_C==2'b10)?reg0_ALU_result:
    MEM_DATA;
    
  cache D_cache(
    .i_clk(i_clk),
    .i_rst(i_rst),
    .i_mem_ready(i_dmem_ready),
    .o_mem_addr(o_dmem_addr),
    .o_mem_ren(o_dmem_ren),
    .o_mem_wen(o_dmem_wen),
    .o_mem_wdata(o_dmem_wdata),
    .i_mem_rdata(i_dmem_rdata),
    .i_mem_valid(i_dmem_valid),
    .o_busy(d_cache_stall),
    .i_req_addr(reg0_aligned_address),
    .i_req_ren(reg1_MemRead_C),
    .i_req_wen(reg1_MemWrite_C),
    .i_req_mask(reg0_mask),
    .i_req_wdata(reg0_WriteDataMem),
    .o_res_rdata(MEM_DATA)
  );



  //assign o_dmem_addr = reg0_aligned_address;  //assign memory adress port to ALU result 
  //wire dmem_ren; 
  //assign dmem_ren=reg1_MemRead_C;
  //assign o_dmem_ren  = dmem_ren;   //assign Memory Read enable signal 
  //assign dmem_wen = reg1_MemWrite_C;
  //assign o_dmem_wen  = reg1_MemWrite_C;  //assign Memory Write enable signal 
  //assign o_dmem_wdata = reg0_WriteDataMem;     //assign Memory Write data port to register output #2
  //assign MEM_DATA = i_dmem_rdata;    //data returned from memory 



/* 
 MEM/WB pipeline register  
*/
reg [1:0]  reg2_Data_sel_C;
reg [31:0] reg0_MEM_DATA;
reg [31:0] reg1_ALU_result;
reg [31:0] reg2_immediate_val;
reg [31:0] reg3_PC_plus4; 
reg reg3_retire_valid;
reg [31:0] reg3_current_PC;
reg [31:0] reg1_aligned_address;
reg reg2_MemRead_C;
reg reg2_MemWrite_C;
reg [31:0] reg1_WriteDataMem;

reg [31:0] reg2_regData1;
reg [31:0] reg2_regData2;

always @(posedge i_clk) begin
    if (i_rst)begin
      reg2_regWrite         <= 1'd0;
      reg2_Data_sel_C       <= 2'd0;
      reg0_MEM_DATA         <= 32'd0; 
      reg1_ALU_result       <= 32'd0;
      reg2_immediate_val    <= 32'd0;
      reg3_PC_plus4         <= 32'd0;
      reg1_mask             <= 4'd0;
      reg1_byte_hw_unsigned <= 1'd0;
      reg3_curr_instruct    <= 32'd0; 
      reg3_retire_valid     <= 1'd0;
      reg3_current_PC       <= 32'd0;  
      reg1_aligned_address  <= 32'd0;
      reg2_MemRead_C        <= 1'd0; 
      reg2_MemWrite_C       <= 1'd0;
      reg1_WriteDataMem     <= 32'd0;
      reg2_regData1         <= 32'd0;
      reg2_regData2         <= 32'd0;   
    end else if (~d_cache_stall) begin
      reg2_regWrite         <= reg1_regWrite;
      reg2_Data_sel_C       <= reg1_Data_sel_C; 
      reg0_MEM_DATA         <= MEM_DATA;
      reg1_ALU_result       <= reg0_ALU_result;
      reg2_immediate_val    <= reg1_immediate_val; 
      reg3_PC_plus4         <= reg2_PC_plus4;
      reg1_mask             <= reg0_mask;
      reg1_byte_hw_unsigned <= reg0_byte_hw_unsigned;
      reg3_curr_instruct    <= reg2_curr_instruct; 
      reg3_retire_valid     <= reg2_retire_valid;
      reg3_current_PC       <= reg2_current_PC;
      reg1_aligned_address  <= reg0_aligned_address;
      reg2_MemRead_C        <= reg1_MemRead_C;
      reg2_MemWrite_C       <= reg1_MemWrite_C;
      reg1_WriteDataMem     <= reg0_WriteDataMem; 
      reg2_regData1         <= reg1_regData1;
      reg2_regData2         <= reg1_regData2;
    end 
 end


  /* 
 Instantiate WB section of proccesor 
*/
  WB writeback (

      .i_MemData(MEM_DATA),  //input-  data coming from Memory
      .i_AluRslt(reg1_ALU_result),  //input- ALU operation result 
      .i_imm(reg2_immediate_val),  //input- output from immediate generator 
      .i_PC4(reg3_PC_plus4),  //input- incremented PC (used to save jump return adress in register)
      .i_MUXsel(reg2_Data_sel_C),  //input- MUX select signals coming from control unit 

      .o_dataSel(WB_DATA)        //output- data selected from mux to feedback into write port of Register file
  );


  /*
THIS section still needs to be checked and filled in properly (some values are being used as placeholders for now)
We can add extra output signals from modules to connect below 
*/
 // assign o_dmem_mask = reg0_mask; //this used to control half word/byte loads and write (set to full word only for now)


  assign o_retire_valid = reg3_retire_valid &  ~i_rst; //one instruction should be done every cycle
  assign o_retire_inst = reg3_curr_instruct;
  assign o_retire_trap = 1'b0;  // implement trap detection later
  assign o_retire_halt = (reg3_curr_instruct == 32'h00100073);  // detect ebreak in ID stage 

  // retire register addresses (taken directly from the instruction fields)
  assign o_retire_rs1_raddr = reg3_curr_instruct[19:15];
  assign o_retire_rs2_raddr = reg3_curr_instruct[24:20];
  assign o_retire_rd_waddr = rf_writeAddress;

  // retire register read data 
  // Ideally use the raw register-file read data
  assign o_retire_rs1_rdata = reg2_regData1;
  assign o_retire_rs2_rdata = reg2_regData2;

  // retire write-back info (what is written back this cycle)
  assign o_retire_rd_wdata = WriteDataReg;

  // retire PC values
  assign o_retire_pc = reg3_current_PC;
  assign o_retire_next_pc = next_PC;

  assign o_retire_dmem_addr = reg1_aligned_address; 
  assign o_retire_dmem_ren = reg2_MemRead_C;
  assign o_retire_dmem_wen = reg2_MemWrite_C;
  assign o_retire_dmem_mask = reg1_mask; 
  assign o_retire_dmem_wdata = reg1_WriteDataMem; 
  assign o_retire_dmem_rdata = MEM_DATA; 



endmodule

`default_nettype wire
