`default_nettype none
module WB(


  input wire[31:0] i_MemData,  //data coming from Memory
  input wire[31:0] i_AluRslt,   //ALU operation result 
  input wire[31:0] i_imm,        //output from immediate generator 
  input wire[31:0] i_PC4,       //incremented PC (used to save jump return adress in register)
  input wire [1:0] i_MUXsel,    //MUX select signals coming from control unit 

  output wire [31:0] o_dataSel // data selected from mux to feedback into write port of Register file
  );

  /*
  4-1 MUX to select what data is fed back into regWrite port 
  00 -> PC+4  (save incremented PC for jump return address)
  01 -> i_imm (save immediate for LUI )  
  10 -> ALU result
  11 -> Data from Memory
  */
  assign o_dataSel = 
   (i_MUXsel == 2'b00) ? i_PC4 
  :(i_MUXsel == 2'b01) ? i_imm
  :(i_MUXsel == 2'b10) ? i_AluRslt : i_MemData;


endmodule
`default_nettype wire