`default_nettype none
module imm_format(
    input wire [6:0] opcode,

    // Instruction format, determined by the instruction decoder based on the
    // opcode. This is one-hot encoded according to the following format:
    // [0] R-type (don't-care, see below)
    // [1] I-type
    // [2] S-type
    // [3] B-type
    // [4] U-type
    // [5] J-type
    output wire [5:0] i_format
);

localparam R_type = 7'b0110011;
localparam I_type = 7'b0010011;
localparam Load   = 7'b0000011; 
localparam S_type = 7'b0100011; 
localparam B_type = 7'b1100011; 
localparam LUI    = 7'b0110111; //(U-type)
localparam auipc  = 7'b0010111; //(U-type)
localparam Jump   = 7'b1101111; //jal
localparam JumpR  = 7'b1100111; //jalr

    assign i_format = (opcode == R_type) ? 6'b000001 : // R-type
                      (opcode == Load || opcode == I_type || opcode == JumpR) ? 6'b000010 : // I-type
                      (opcode ==  S_type) ? 6'b000100 : // S-type
                      (opcode ==  B_type) ? 6'b001000 : // B-type
                      (opcode == LUI || opcode == auipc) ? 6'b010000 : // U-type
                      (opcode == Jump) ? 6'b100000 : // J-type
                      6'b000001; // default to R-type for don't care


endmodule
`default_nettype wire