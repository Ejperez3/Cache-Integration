`default_nettype none

module IF(
  input wire IF_EN,
  input wire i_clk,           //clk to control PC update
  input wire i_rst,           //used to reset PC to starting value
  input wire [31:0] i_NextPC,      //next adress for PC either PC+4 or branch/jump PC

  output reg [31:0] o_PC,          //current PC will feed into instruction memory and other locations (schematic) 
  output wire [31:0] o_inc_pc  //Output current PC + 4 
);

always @(posedge i_clk) begin
    if (i_rst) begin
        o_PC <= 32'h00000000;  // reset PC
    end else if (IF_EN) begin
        o_PC <= i_NextPC;      // update PC when IF_EN is 1
    end else begin
        o_PC <= o_PC;           // hold PC (synchronous stall)
    end
end

  assign o_inc_pc = o_PC + 32'd4;

endmodule
`default_nettype wire

