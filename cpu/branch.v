`default_nettype none
// Branch control Module
// as per schematic, bits are read from
// right to left (2 mux's)
//00   PC+4
//10   PC+4
//01   JALR o_result from ALU
//11   Branch PC+Imm & JAL

module branch (
    input wire [2:0] func3,
    input wire jal,
    input wire jalr,
    input wire branch,
    input wire eq,
    input wire slt,

    output wire [1:0] out
);

  assign out=
    (jal)?(2'b11):
    (jalr)?(2'b01): //DOUBLE CHECK THIS: SHOULD BE OUTPUT OF REGISTER, IE THROUGH ALU
    (branch & func3==3'b000)? (eq?  2'b11: 2'b00):
    (branch & func3==3'b001)? (~eq ? 2'b11: 2'b00):
    (branch & func3==3'b100)? (slt ? 2'b11: 2'b00):
    (branch & func3==3'b101)? ((~slt || eq) ? 2'b11:2'b00):
    (branch & func3==3'b110)? (slt ? 2'b11 : 2'b00) :
    (branch & func3==3'b111)? ((~slt||eq) ? 2'b11:2'b00):
    2'b00;
endmodule
`default_nettype wire
