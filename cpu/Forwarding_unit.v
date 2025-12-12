`default_nettype none

/*
This unit should overide any hazard detection (can do this by AND with hazard signal to create new stalling signal)
With forwarding stalls should only occur on load-use hazard
*/
module Forwarding_unit (
  input wire[6:0] op_code,

    //When the instruction reaches EX, it checks if its rs1 or rs2 register matches the rd register of any instruction ahead 
    //in the pipeline (EX/MEM or MEM/WB) If yes — we take that newer value instead of the stale one from the register file.

    input wire reg_enable_1,
    input wire reg_enable_2,
    input wire [4:0] IDEX_RS1,  //rs1 read reg in EX
    input wire [4:0] IDEX_RS2,  //rs2 read reg in eX

    input wire [4:0] EXMEM_RD,  //future RD registers 
    input wire [4:0] MEMWB_RD,

    input wire EXMEM_regWrite,  //Write enable signals 
    input wire MEMWB_regWrite,

    input wire [31:0] EXMEM_aluResult,
    input wire [31:0] MEMWB_wbValue,


    output wire FW1_mux_sel,
    output wire FW2_mux_sel,
    output wire [31:0] FW_data1,
    output wire [31:0] FW_data2,
    output wire FW3_mux_sel
);

  wire forward_det1;
  wire forward_det2;
  wire forward_det3;
  wire forward_det4;


  //Forwarding possibilities 
  assign forward_det1 = (IDEX_RS1 == EXMEM_RD) && (EXMEM_RD != 5'd0) && (EXMEM_regWrite);
  assign forward_det2 = (IDEX_RS1 == MEMWB_RD) && (MEMWB_RD != 5'd0) && (MEMWB_regWrite);

  assign forward_det3 = (IDEX_RS2 == EXMEM_RD) && (EXMEM_RD != 5'd0) && (EXMEM_regWrite);
  assign forward_det4 = (IDEX_RS2 == MEMWB_RD) && (MEMWB_RD != 5'd0) && (MEMWB_regWrite);
  assign FW3_mux_sel=((op_code==7'b0100011) && (forward_det3 || forward_det4)) ? 1'b1 : 1'b0;

  //check if we need to forward RS1
  assign FW1_mux_sel = (~(reg_enable_1) && (forward_det1 || forward_det2)) ? 1'b1 : 1'b0;

  //checl if we need to forward RS2
  assign FW2_mux_sel = (~(reg_enable_2) && (forward_det3 || forward_det4)) ? 1'b1 : 1'b0;


  assign FW_data1 = (forward_det1) ? EXMEM_aluResult :
                  (forward_det2) ? MEMWB_wbValue   :
                                   32'd0; //no forwarding needed will choose default

  assign FW_data2 = (forward_det3) ? EXMEM_aluResult :
                  (forward_det4) ? MEMWB_wbValue   :
                                   32'd0; //no forwarding needed will choose default
endmodule
`default_nettype wire
