// Hazard enabled IF
// ID/EX.WriteReg == IF/ID.RegisterRs1 or IF/ID.RegisterRs2
// OR
// Ex/MEM.WriteReg==IF/ID.RegisterRs1 or iF/ID.RegisterRs2
//
// if ~i_mem_ready && i_o_imem_ren, STALL
// if 

// TODO: UPDATE FOR FORWARDING/BYPASSING LATER
module hazard (
    input wire [6:0] op_code,
    input wire [4:0] IF_ID_RS1,
    input wire [4:0] IF_ID_RS2,
    input wire valid_inst,

    input wire [4:0] ID_EX_WriteReg,
    input wire       ID_EX_MemRead,

    //NOTE: disable the PC if the IF memory stalls
    output wire PC_En,
    output wire IF_ID_En,
    output wire Mux_sel,
    input wire i_cache_stall
);

  wire is_jump_or_lui;
  assign is_jump_or_lui=(op_code==(7'b0110111)|| op_code==7'b0010111 || op_code==7'b1101111);

  wire load_use_hazard;
  assign load_use_hazard = valid_inst && (~is_jump_or_lui) && (ID_EX_MemRead) && ((ID_EX_WriteReg == IF_ID_RS1) || (ID_EX_WriteReg == IF_ID_RS2)) && (ID_EX_WriteReg != 5'd0);

  assign PC_En = ~(load_use_hazard||i_cache_stall);
  assign IF_ID_En = ~(load_use_hazard||i_cache_stall);
  assign Mux_sel = (load_use_hazard||i_cache_stall);


  //if the memory is busy, just stall
  //if the instruction memory is busy
  //1) disable the PC
  //2) disable the MUX, forcing it to select to maintin the current PC


endmodule

