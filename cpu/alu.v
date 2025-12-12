`default_nettype none

// The arithmetic logic unit (ALU) is responsible for performing the core
// calculations of the processor. It takes two 32-bit operands and outputs
// a 32 bit result based on the selection operation - addition, comparison,
// shift, or logical operation. This ALU is a purely combinational block, so
// you should not attempt to add any registers or pipeline it in phase 3.
module alu (
    // Major operation selection.
    // NOTE: In order to simplify instruction decoding in phase 4, both 3'b010
    // and 3'b011 are used for set less than (they are equivalent).
    // Unsigned comparison is controlled through the `i_unsigned` signal.
    //
    // 3'b000: addition/subtraction if `i_sub` asserted
    // 3'b001: shift left logical
    // 3'b010,
    // 3'b011: set less than/unsigned if `i_unsigned` asserted
    // 3'b100: exclusive or
    // 3'b101: shift right logical/arithmetic if `i_arith` asserted
    // 3'b110: or
    // 3'b111: and
    input  wire [ 2:0] i_opsel,
    // When asserted, addition operations should subtract instead.
    // This is only used for `i_opsel == 3'b000` (addition/subtraction).
    input  wire        i_sub,
    // When asserted, comparison operations should be treated as unsigned.
    // This is only used for branch comparisons and set less than.
    // For branch operations, the ALU result is not used, only the comparison
    // results.
    input  wire        i_unsigned,
    // When asserted, right shifts should be treated as arithmetic instead of
    // logical. This is only used for `i_opsel == 3'b011` (shift right).
    input  wire        i_arith,
    // First 32-bit input operand.
    input  wire [31:0] i_op1,
    // Second 32-bit input operand.
    input  wire [31:0] i_op2,
    // 32-bit output result. Any carry out (from addition) should be ignored.
    output wire [31:0] o_result,
    // Equality result. This is used downstream to determine if a
    // branch should be taken.
    output wire        o_eq,
    // Set less than result. This is used downstream to determine if a
    // branch should be taken.
    output wire        o_slt
);

  //assigning o eq
  assign o_eq = (i_op1 == i_op2);


  //logic to asing o_slt
  wire signed [31:0] signed_op1 = i_op1;
  wire signed [31:0] signed_op2 = i_op2;

  wire slt_signed = (signed_op1 < signed_op2);
  wire slt_unsigned = (i_op1 < i_op2);

  assign o_slt = i_unsigned ? slt_unsigned : slt_signed;

  //add/subtract
  wire [31:0] op2_mux = i_sub ? ~i_op2 + 1 : i_op2;
  wire [31:0] add_sub_result = i_op1 + op2_mux;

  //logic ops
  wire [31:0] and_result = i_op1 & i_op2;
  wire [31:0] or_result = i_op1 | i_op2;
  wire [31:0] xor_result = i_op1 ^ i_op2;


  //shift ops
  wire [31:0] shift_result;
  wire shift_left;

  assign shift_left = (i_opsel == 3'b001) ? 1'b1 : 1'b0;

  barrel_shifter shifter (
      .i_value(i_op1),
      .i_shift_amt(i_op2[4:0]),
      .i_left(shift_left),
      .i_arith(i_arith),
      .o_result(shift_result)
  );

  //output
  wire is_shift;
  assign is_shift = (i_opsel == 3'b001) | (i_opsel == 3'b101);

  assign o_result = (i_opsel == 3'b000) ? add_sub_result :  //add/sub
      (i_opsel == 3'b111) ? and_result :  //and
      (i_opsel == 3'b110) ? or_result :  //or
      (i_opsel == 3'b100) ? xor_result :  //xor
      (is_shift) ? shift_result :  //shift ops
      {{31'b0}, o_slt};  //slt (only option left)

endmodule

module barrel_shifter (
    input wire [31:0] i_value,
    input wire [4:0] i_shift_amt,
    input wire i_left,
    input wire i_arith,
    output wire [31:0] o_result
);
  wire [31:0] stage[4:0];

  //first stage
  assign stage[0] = i_shift_amt[0] ? (i_left ? {i_value[30:0], 1'b0} :  //left shift
      (i_arith ? {i_value[31], i_value[31:1]} :  //righ arithmetic shift
      {1'b0, i_value[31:1]}))  //right logical shift
      : i_value;

  //second stage
  assign stage[1] = i_shift_amt[1] ? (i_left ? {stage[0][29:0], 2'b0} :  //left shift
      (i_arith) ? {{2{stage[0][31]}}, stage[0][31:2]} :  //right arithmetic shift
      {2'b0, stage[0][31:2]}) :  //right logical shift
      stage[0];

  //third stage
  assign stage[2] = i_shift_amt[2] ? (i_left ? {stage[1][27:0], 4'b0} :  //left shift
      (i_arith ? {{4{stage[1][31]}}, stage[1][31:4]} :  //right arithmetic shift
      {4'b0, stage[1][31:4]})) :  //right logical shift 
      stage[1];

  //fourth stage
  assign stage[3] = i_shift_amt[3] ? (i_left ? {stage[2][23:0], 8'b0} :  //left shift
      (i_arith ? {{8{stage[2][31]}}, stage[2][31:8]} :  //right arithmetic shift
      {8'b0, stage[2][31:8]})) :  //right logical shift
      stage[2];

  //fifth stage
  assign stage[4] = i_shift_amt[4] ? (i_left ? {stage[3][15:0], 16'b0} :  //left shift
      (i_arith ? {{16{stage[3][31]}}, stage[3][31:16]} :  //right arithmetic shift
      {16'b0, stage[3][31:16]})) :  //right logical shift
      stage[3];

  assign o_result = stage[4];

endmodule






`default_nettype wire
