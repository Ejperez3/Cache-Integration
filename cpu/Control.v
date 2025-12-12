`default_nettype none
//000 for R   opcode: 011 0011
//001 for I   opcode: 001 0011       load: 000 0011
//010 for S   opcode: 010 0011 
//011 for B   opcode: 110 0011
//100 for U   opcode: Lui: 011 0111  auipc: 001 0111
//101 for J   opcode: 110 1111   jalr:110 0111

module Control (

    //module inputs 
    input wire [6:0] i_opcode,

    //module outputs 
    output wire jal,  //feeds into branch logic
    output wire jalr,  //feeds into branch logic
    output wire branch,  //feeds into branch logic
    output wire MemRead,
    output wire MemWrite,
    output wire ALUsrc2,
    output wire ALUsrc1,
    output wire RegWrite,
    output wire [1:0] Data_sel,
    output wire [2:0] ALUOp
);

  localparam R_type = 7'b0110011;
  localparam I_type = 7'b0010011;
  localparam Load = 7'b0000011;
  localparam S_type = 7'b0100011;
  localparam B_type = 7'b1100011;
  localparam LUI = 7'b0110111;  //(U-type)
  localparam auipc = 7'b0010111;  //(U-type)
  localparam Jump = 7'b1101111;  //jal
  localparam JumpR = 7'b1100111;  //jalr

  assign jal = (i_opcode == Jump);  //check if jal instruction 
  assign jalr = (i_opcode == JumpR);  //check if jalr instruction
  assign branch = (i_opcode == B_type);  //check if branch instruction 
  assign MemRead = (i_opcode == Load);  //check if load instruction 
  assign MemWrite = (i_opcode == S_type);  //check if store instruction

  //chooses between register1 and PC
  assign ALUsrc1 = (i_opcode == auipc);  //only use pc as alu operand for auipc

  //set high for Immediate, Load, and Store
  assign ALUsrc2 = (i_opcode == I_type) || (i_opcode == Load) || (i_opcode == S_type) || (i_opcode==auipc);

  //enable register write if one of the following instructions else sets to 0
  assign RegWrite = (i_opcode == R_type) ||  //check if R-type
      (i_opcode == I_type) ||  //check if i-type
      (i_opcode == Load) ||  //check if Load
      (i_opcode == Jump) ||  //check if Jal instruction (J-type)
      (i_opcode == JumpR)  ||  //check if jalr instruction (need to save PC+4 in register 1 for jumps)
      (i_opcode == LUI) || (i_opcode == auipc);

  /*
operation type depending on opcode:  
Set 3'000 for R   
Set 3'001 for I   
Set 3'010 for S   
Set 3'011 for B   
Set 3'100 for U   
Set 3'101 for J   
*/
  assign ALUOp    =    (i_opcode == R_type) ? 3'b000 : 
                     (i_opcode == I_type) ? 3'b001 : 
                     (i_opcode == Load)   ? 3'b111 : //load is I_type set to same value
      (i_opcode == S_type) ? 3'b010 :
                     (i_opcode == B_type) ? 3'b011 :
                     (i_opcode == LUI)    ? 3'b100 : //U-type
      (i_opcode == auipc) ? 3'b100 :  //U-type
      (i_opcode == Jump)   ? 3'b101 : 
                     (i_opcode == JumpR)  ? 3'b001 : 3'b000;  // JumpR considered I-Type instruction 


  /*
Controls mux that selects wich data is goes to Write_data port of register file
2'b11 -> selects data from memory 
2'b10 -> selects ALU output result 
2'b01 -> selects immediate output (used for one U-type)
2'b00 -> selects pc+4 (used in jump instructions)
*/
  assign Data_sel    = (i_opcode == R_type) ? 2'b10 : 
                     (i_opcode == I_type) ? 2'b10 : 
                     (i_opcode == Load)   ? 2'b11 : 
                     (i_opcode == auipc)  ? 2'b10 :
                     (i_opcode == LUI)    ? 2'b01 :
                     (i_opcode == Jump)   ? 2'b00 : 
                     (i_opcode == JumpR)  ? 2'b00 : 2'b10;

endmodule

`default_nettype wire
