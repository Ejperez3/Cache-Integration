`default_nettype none
module MEM(

  /* 
    Actual memory interface will be inside hart.v module 
    Designer can choose to just pass through input signals such as i_Memwrite since nothing will be done with 
    memory inside this file (to stay consistent) or remove completly from this module and interface inside hart.v
  */

  input wire [31:0] i_aluResult,//Output from ALU can be used for either memory adress or multiplexed to next PC
  input wire [31:0] i_PC4,       //previous PC+4 used as input for multiplexer
  input wire [31:0] i_PCimm,     //previous PC+imm used as input for multiplexer 
  input wire [1:0] i_MUXpc,    //select signal used to select next PC


  output wire [31:0] o_nxtPC //the next PC based off Mux select signals 
  
  );

  //intermidiate signal between MUX 1 and 2
  wire [31:0] Mux1Select; 

  assign Mux1Select = (i_MUXpc[0]) ?  i_PC4 : i_PCimm;
 
  assign o_nxtPC = (i_MUXpc[1]) ?  Mux1Select : i_aluResult; //assign next PC value

endmodule

`default_nettype wire
