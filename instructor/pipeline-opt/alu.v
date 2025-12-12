`default_nettype none

// The arithmetic logic unit (ALU) is responsible for performing the core
// calculations of the processor. It takes two 32-bit operands and outputs
// a 32 bit result based on the selection operation - addition, comparison,
// shift, or logical operation. This ALU is a purely combinational block, so
// you should not attempt to add any registers or pipeline it in Lab 0.
module alu (
    // Major operation selection.
    // 3'b000: addition/subtraction if `i_sub` asserted
    // 3'b001: shift left logical
    // 3'b010: set less than
    // 3'b011: set less than unsigned
    // 3'b100: exclusive or
    // 3'b101: shift right logical/arithmetic if `i_arith` asserted
    // 3'b110: or
    // 3'b111: and
    input  wire [ 2:0] i_opsel,
    // When asserted, addition operations should subtract instead.
    // This is only used for `i_opsel == 3'b000` (addition/subtraction).
    input  wire        i_sub,
    // When asserted, comparison operations should be treated as unsigned.
    // This is only used for branch comparisons, as the set less than unsigned
    // mode is already specified by `i_opsel`. For branch operations, the ALU
    // result is not used, only the comparison results.
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
    // Reference implementation, do not distribute.
    // TODO: This has not been tested.

    // Combined adder unit that performs arithmetic add/sub, set less than
    // comparisons, and branch comparison.
    // To do so, the 32 bit operands are first sign or zero extended to 33
    // bits (based on the comparison mode), and then the sign of the result is
    // checked to determine the comparison result.
    wire zext = i_unsigned | (i_opsel == 3'b011);
    wire [32:0] add_op1 = {i_op1[31] & ~zext, i_op1};
    wire [32:0] add_op2 = {i_op2[31] & ~zext, i_op2} ^ {33{i_sub}};
    wire [32:0] sum     = add_op1 + add_op2 + i_sub;
    wire [31:0] add_result = sum[31:0]; // addition throws away the carry out

    // The comparison result is the sign of the 33 bit sum.
    wire slt = sum[32];
    wire [31:0] slt_result = {31'b0, slt};

    // Logical operations are straightforward.
    wire [31:0] xor_result = i_op1 ^ i_op2;
    wire [31:0] or_result  = i_op1 | i_op2;
    wire [31:0] and_result = i_op1 & i_op2;

    // Equality comparison can use the xor result and check for zero.
    wire eq = xor_result == 32'b0;

    // The shifter is is a simple logarithmic barrel shifter.
    wire dir = i_opsel[2]; // 0 for left shift, 1 for right shift
    wire [31:0] shift_result;
    barrel barrel (
        .i_operand(i_op1),
        .i_shamt(i_op2[4:0]),
        .i_dir(dir),
        .i_arith(i_arith),
        .o_result(shift_result)
    );

    reg [31:0] result;
    always @(*) begin
        result = 32'hx;

        case (i_opsel)
            3'b000: result = add_result;
            3'b001: result = shift_result;
            3'b010,
            3'b011: result = slt_result;
            3'b100: result = xor_result;
            3'b101: result = shift_result;
            3'b110: result = or_result;
            3'b111: result = and_result;
        endcase
    end

    assign o_result = result;
    assign o_eq = eq;
    assign o_slt = slt;
endmodule

// The shifter is implemented as a barrel shifter that cascades a set of
// multiplexers, one per input bit of the shift amount. By either shifting or
// not shifting by that bit, the final variable shift result is obtained.
// Shift left and right are implemented separately, as combining them with
// a rotate and mask is complex and unlikely to yield significant savings.
module barrel (
    // Input 32-bit operand to be shifted.
    input  wire [31:0] i_operand,
    // Input 5-bit shift amount.
    input  wire [ 4:0] i_shamt,
    // Direction to shift. This is asserted for right shifts.
    input  wire        i_dir,
    // When asserted, right shifts should be arithmetic instead of logical.
    input  wire        i_arith,
    // Output 32-bit shifted result.
    output wire [31:0] o_result
);
    wire [31:0] sli = i_operand;
    wire [31:0] sl4 = i_shamt[4] ? {sli[15:0], 16'b0} : sli;
    wire [31:0] sl3 = i_shamt[3] ? {sl4[23:0],  8'b0} : sl4;
    wire [31:0] sl2 = i_shamt[2] ? {sl3[27:0],  4'b0} : sl3;
    wire [31:0] sl1 = i_shamt[1] ? {sl2[29:0],  2'b0} : sl2;
    wire [31:0] sl0 = i_shamt[0] ? {sl1[30:0],  1'b0} : sl1;

    wire sign = i_operand[31] & i_arith;
    wire [31:0] sri = i_operand;
    wire [31:0] sr4 = i_shamt[4] ? {{16{sign}}, sri[31:16]} : sri;
    wire [31:0] sr3 = i_shamt[3] ? {{ 8{sign}}, sr4[31: 8]} : sr4;
    wire [31:0] sr2 = i_shamt[2] ? {{ 4{sign}}, sr3[31: 4]} : sr3;
    wire [31:0] sr1 = i_shamt[1] ? {{ 2{sign}}, sr2[31: 2]} : sr2;
    wire [31:0] sr0 = i_shamt[0] ? {{ 1{sign}}, sr1[31: 1]} : sr1;

    assign o_result = i_dir ? sr0 : sl0;
endmodule

`default_nettype wire
