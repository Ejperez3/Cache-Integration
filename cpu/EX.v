`default_nettype none

module EX (
    input wire[31:0] i_pc,    //Current PC input should be added to immediate (used for branch instructions)
    input wire [2:0] func3,  //func 3 input for branch logic block (branch.v file)
    input wire i_jal,  //control signal for branch logic block
    input wire i_jalr,  //control signal for branch logic block
    input wire i_branch,  //control signal for branch logic block
    input wire [2:0] i_ALUOp,  //input to ALU CTRL unit
    input wire [31:0] i_op1,  //ALU operand1
    input wire [31:0] i_op2,  //ALU operand2
    input wire[31:0] i_imm,//i_imm is used for adding to current PC if we are in I instruction i_op2 will be input as immediate already
    input wire [3:0] func,  //combination of func7 and func 3 used by ALU control

    /* 
 Outputs defined below
 */
    output wire [31:0] o_result,  //connect to ALU
    output wire [1:0] o_PC_Select,  //output of Branch logic unit used to select next PC
    output wire [31:0] o_inc_pc  //The inputted PC + Immediate (used for branch adress calculation)
);

  //internal wire connections
  wire o_sub;
  wire o_unsigned;
  wire o_arith;
  wire [2:0] o_opsel;
  wire o_eq;  //connect to ALU
  wire o_slt;  //connect to ALU

  //instantiate ALU control module
  alu_control ALU_cntrl (
      .instruction_bits(func),
      .alu_op(i_ALUOp),
      .o_sub(o_sub),
      .o_unsigned(o_unsigned),
      .o_arith(o_arith),
      .o_opsel(o_opsel)
  );

  //instantiate ALU module
  alu ALU (
      .i_opsel(o_opsel),
      .i_sub(o_sub),
      .i_unsigned(o_unsigned),
      .i_arith(o_arith),
      .i_op1(i_op1),
      .i_op2(i_op2),
      .o_result(o_result),
      .o_eq(o_eq),
      .o_slt(o_slt)
  );

  //instantiate branch module
  branch BRANCH (
      .func3(func3),
      .jal(i_jal),
      .jalr(i_jalr),
      .branch(i_branch),
      .eq(o_eq),
      .slt(o_slt),
      .out(o_PC_Select)
  );

  //PC + immediate for branch instructions
  assign o_inc_pc = i_pc + i_imm; 


endmodule

`default_nettype wire

