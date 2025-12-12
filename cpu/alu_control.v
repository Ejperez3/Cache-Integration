`default_nettype none

module alu_control (
    //bits [30, 14:12] of instruction, 30 is funct7[5], 14:12 is funct3
    input wire [3:0] instruction_bits,

    //000 for R
    //001 for I
    //010 for S
    //011 for B 
    //100 for U
    //101 for J
    input wire [2:0] alu_op,

    // When asserted, comparison operations should be treated as unsigned.
    // This is only used for branch comparisons and set less than.
    // For branch operations, the ALU result is not used, only the comparison
    // results.
    //
    //NOTE: only asserted for comp and slt, ie  
    output wire o_unsigned,

    // When asserted, addition operations should subtract instead.
    // This is only used for `i_opsel == 3'b000` (addition/subtraction).
    output wire o_sub,

    // When asserted, right shifts should be treated as arithmetic instead of
    // logical. This is only used for `i_opsel == 3'b011` (shift right).
    //
    output wire o_arith,

    // 3'b000: addition/subtraction if `i_sub` asserted 
    // 3'b001: shift left logical 
    // 3'b010, set less than 
    // 3'b011: set less than/unsigned if `i_unsigned` asserted 
    // 3'b100: exclusive or 
    // 3'b101: shift right logical/arithmetic if `i_arith` asserted 
    // 3'b110: or 
    // 3'b111: and 
    output wire [2:0] o_opsel
);

  wire [2:0] sbuj_type;  //for S, B, U, J type instructions

  wire [2:0] func3;
  assign func3 = instruction_bits[2:0];  //func 3 bits pulled out 

  //Arithmetic shift right only for I and R type instructions 
  assign o_arith = instruction_bits[3] && (alu_op == 3'b000 || alu_op == 3'b001);

  //set for following: 
  //R type and func3 = 011 (sltu)
  //I Type and func3 = 011 (sltiu)
  //B type and func3 = 110 (bltu)
  //B type and func3 = 111 (bgeu)  
  assign o_unsigned = (alu_op == 3'b000 && func3 == 3'b011) || 
                      (alu_op == 3'b001 && func3 == 3'b011) ||
                      (alu_op == 3'b011 && func3 == 3'b110) ||
                      (alu_op == 3'b011 && func3 == 3'b111);

  //Only set subtraction when in R type and func7 bit is set
  assign o_sub = instruction_bits[3] && (alu_op == 3'b000);


  assign sbuj_type = 3'b000;
  assign o_opsel =(alu_op==3'b111)?3'b000:((alu_op == 3'b000 || alu_op == 3'b001) ? func3 : sbuj_type);


endmodule

`default_nettype wire
