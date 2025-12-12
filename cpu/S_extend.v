`default_nettype none

module S_extend(
  input wire [3:0] i_mask,         
  input wire i_unsign,
  input wire [3:0] i_old_mask,
  input wire i_old_unsign,


  input wire [31:0] i_Rs2Data,   //register data input 
  output wire[31:0] o_Memdata,   //aligned output based on mask 
  input wire [31:0] i_WB,
  output wire [31:0] o_regData
);

assign o_Memdata = (i_mask == 4'b1111)?  i_Rs2Data :
                   (i_mask == 4'b1100)? { i_Rs2Data[15:0] , 16'h0}:
                   (i_mask == 4'b0011)? { {16{i_Rs2Data[15]}} ,i_Rs2Data[15:0] }:
                   (i_mask == 4'b0001)? { {24{i_Rs2Data[7]}} ,i_Rs2Data[7:0]  }:
                   (i_mask == 4'b0010)? { {16{i_Rs2Data[7]}} ,i_Rs2Data[7:0] , 8'h0 }:
                   (i_mask == 4'b0100)? { {8{i_Rs2Data[7]}} ,i_Rs2Data[7:0] , 16'h0 }:
                   (i_mask == 4'b1000)? { i_Rs2Data[7:0], 24'h0 }:
                   i_Rs2Data; 


assign o_regData = (i_old_mask ==  4'b1111) ? i_WB : 
                   ((i_old_mask == 4'b0011)  &  i_old_unsign)  ? { 16'h0 ,i_WB[15:0] }:
                   ((i_old_mask == 4'b0011)  & ~i_old_unsign)  ? { {16{i_WB[15]}} , i_WB[15:0] } :
                   (i_old_mask  == 4'b1100   & i_old_unsign)   ? {  16'h0,i_WB[31:16] }:
                   (i_old_mask  == 4'b1100   & ~i_old_unsign)  ? {  {16{i_WB[15]}},i_WB[31:16] }:
                   ((i_old_mask == 4'b0001)  & ~i_old_unsign ) ? { {24{i_WB[7]}} ,i_WB[7:0]} : 
                   ((i_old_mask == 4'b0001)  & i_old_unsign)   ? { 24'h0, i_WB[7:0]} :
                   ((i_old_mask == 4'b0010)  & ~i_old_unsign)  ? { {16{i_WB[7]}} ,i_WB[7:0], 8'h0 }: 
                   ((i_old_mask == 4'b0010)  & i_old_unsign)   ? { 16'h0 ,i_WB[7:0], 8'h0 }:
                   ((i_old_mask == 4'b0100)  & ~i_old_unsign)  ? { {8{i_WB[7]}} ,i_WB[7:0], 16'h0 }:
                   ((i_old_mask == 4'b0100)  & i_old_unsign)   ? { 8'h0 ,i_WB[7:0], 16'h0 }:
                   (i_old_mask ==  4'b1000)                ? {i_WB[7:0], 24'h0} 
                    :i_WB; 






endmodule
`default_nettype wire
