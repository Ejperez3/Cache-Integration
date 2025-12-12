`default_nettype none
module ID (
    input wire        rst,          //input to RF
    input wire        clk,          //input to RF
    input wire [31:0] i_instruct,   //full instruction input
    input wire [31:0] i_currentPC,  //the current PC value (used for auipc instruction)
    input wire [31:0] i_regData1,   //read data1 from register
    input wire [31:0] i_regData2,   //read data2 from register 

    output wire        o_jal,
    output wire        o_jalr,      //output from control unit
    output wire        o_branch,    //output from control unit
    output wire        o_MemRead,   //output from control unit
    output wire [ 1:0] o_Data_sel,  //output from control unit used for WB module
    output wire        o_MemWrite,  //output from control unit
    output wire [31:0] o_op1,       //output from control unit (select ALU operand)
    output wire [31:0] o_op2,       //output from control unit (selects ALU operand)
    output wire [ 2:0] o_ALUop,     //output from control unit goes to ALU control
    output wire [31:0] o_imm,       //the generated immediate 
    output wire [31:0] o_Rdata2,    // will feed into memory 'write data' port 
    output wire        o_RegWrite,  //enable signal for register writing
    output wire        ALUmux1,
    output wire        ALUmux2,

    output wire [3:0] func,
    output wire [2:0] func3
);

  wire [5:0] OneHotDecode;  //used when converting from opcode to instructin type

  //instantiate decoder?
  Control decoder (
      .i_opcode(i_instruct[6:0]),
      .jal(o_jal),
      .jalr(o_jalr),
      .branch(o_branch),
      .MemRead(o_MemRead),
      .MemWrite(o_MemWrite),
      .ALUsrc1(ALUmux1),
      .ALUsrc2(ALUmux2),
      .RegWrite(o_RegWrite),
      .Data_sel(o_Data_sel),
      .ALUOp(o_ALUop)
  );


  // Instruction format, determined by the instruction decoder based on the
  // opcode. This is one-hot encoded according to the following format:
  // [0] R-type (don't-care, see below)
  // [1] I-type
  // [2] S-type
  // [3] B-type
  // [4] U-type
  // [5] J-type
  imm_format OneHot (
      .opcode(i_instruct[6:0]),
      .i_format(OneHotDecode)  //ouput of imm_format
  );

  //instantiate imm_gen
  imm imm_gen (
      .i_inst     (i_instruct),    //full instruction
      .i_format   (OneHotDecode),  //instruction type input
      .o_immediate(o_imm)          //generated immediate 
  );

  //func 3 input to branch logic block
  assign func3 = {i_instruct[14:12]};

  //combination of func7 and func3 for ALU CTRL
  assign func = {i_instruct[30], i_instruct[14:12]};

  //feeds into memory write data port
  assign o_Rdata2 = i_regData2;

  //if 1 current PC else reagister read 1
  assign o_op1 = (ALUmux1) ? i_currentPC : i_regData1;  //mux for ALU operand

  //if 1 take immediate else register read2
  assign o_op2 = (ALUmux2) ? o_imm : i_regData2;

endmodule

`default_nettype wire
