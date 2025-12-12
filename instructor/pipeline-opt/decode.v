/* Author: cmaggard */
/* Last Changed: 7/10/25 */
/* Rev: 0 */

`default_nettype none

module decoder (
    // Input instruction word.
    input  wire [31:0] i_inst,
    // Asserted if the instruction was decoded as a legal instruction. It is
    // important that the decoder not accept any illegal instruction
    // encodings as this could lead to undefined behavior in the processor
    // which is a safety hazard.
    output wire        o_legal,
    // Indicates that the instruction is an ebreak and should halt execution.
    output wire        o_halt,
    // First source register address.
    // For instructions that do not use a source register, this is effectively
    // a don't care because reading unused registers does not have any side
    // effects (and we don't care about power usage, really).
    output wire [ 4:0] o_rs1,
    // Second source register address.
    // Similarly to o_rs1, this is a don't care for instructions that do not
    // read a (second) source register.
    output wire [ 4:0] o_rs2,
    // Destination register address.
    // For instructions that do not write to a register, this must be set to
    // x0 so the value is discarded. This avoids the need for a separate write
    // enable since discard behavior must be present anyway.
    output wire [ 4:0] o_rd,
    // 32-bit immediate value, decoded from the instruction word. For R-type
    // instructions that do not use an immediate, this is a don't care.
    output wire [31:0] o_immediate,
    // Selects whether the first operand for the ALU is fed by the first
    // register source (rs1) or the current pc.
    // When asserted, the second operand is the immediate.
    output wire        o_op1_sel,
    // Selects whether the second operand for the ALU is fed by the second
    // register source (rs2) or the immediate.
    // When asserted, the second operand is the immediate.
    output wire        o_op2_sel,
    // Major opsel for the ALU. See ALU documentation for the encoding.
    output wire [ 2:0] o_alu_opsel,
    // Minor opsel flags for the ALU. See ALU documentation for the encoding.
    output wire        o_alu_sub,
    output wire        o_alu_unsigned,
    output wire        o_alu_arith,
    // If asserted, the instruction is a branch instruction and the PC should
    // be updated to the target address if the branch condition is met.
    output wire        o_branch,
    // If asserted, the instruction is a jump instruction and the PC should
    // be updated to the target address unconditionally.
    output wire        o_jump,
    // When asserted, the branch comparator checks for equality. When not
    // asserted, it checks for less than [unsigned].
    output wire        o_branch_equal,
    // When asserted, the branch comparator treats the less than comparison
    // operands as unsigned. This is only used when `!o_branch_equal`.
    output wire        o_branch_unsigned,
    // When asserted, the branch condition is inverted.
    // Equality -> inequality, less than -> greater than or equal.
    output wire        o_branch_invert,
    // When asserted, the instruction will load from memory.
    output wire        o_dmem_ren,
    // When asserted, the instruction will store to memory.
    output wire        o_dmem_wen,
    // This 2-bit mask selects which LSBs of the memory address should be
    // checked for alignment. This is because byte and half-word accesses need
    // only be 1-byte and 2-byte aligned, respectively.
    output wire [ 1:0] o_dmem_align,
    // These 3 bits select the size of the memory access.
    // They are effectively one-hot encoded.
    output wire        o_dmem_memb,
    output wire        o_dmem_memh,
    output wire        o_dmem_memw,
    // If asserted, the (byte or half-word) memory access is unsigned and the
    // load should be zero-extended to 32 bits instead of sign-extended.
    output wire        o_dmem_memu,
    // Selects the data to write to the destination register, one-hot.
    // [0] = ALU result
    // [1] = immediate
    // [2] = PC + 4
    // [3] = memory
    output wire [ 3:0] o_rd_sel,
    // If asserted, the PC jumps to the target address calculated by the ALU
    // rather than directly to the PC + immediate. This is used for JALR.
    output wire        o_pc_sel
);
    // Reference implementation, do not distribute.
    // For educational reasons, the instruction decoder is primarily
    // implemented using dataflow logic rather than a large behavioral case.
    // This should also lead to a more area efficient implementation as the
    // (open source) logic synthesis tools are not that good at optimization.

    wire [4:0] opcode = i_inst[6:2];
    wire [4:0] rs1    = i_inst[19:15];
    wire [4:0] rs2    = i_inst[24:20];
    wire [4:0] rd     = i_inst[11:7];
    wire [2:0] funct3 = i_inst[14:12];
    wire [6:0] funct7 = i_inst[31:25];

    // major opcode selection
    wire op_load     = opcode == 5'b00000;
    wire op_op_imm   = opcode == 5'b00100;
    wire op_auipc    = opcode == 5'b00101;
    wire op_store    = opcode == 5'b01000;
    wire op_amo      = opcode == 5'b01011;
    wire op_op       = opcode == 5'b01100;
    wire op_lui      = opcode == 5'b01101;
    wire op_branch   = opcode == 5'b11000;
    wire op_jalr     = opcode == 5'b11001;
    wire op_jal      = opcode == 5'b11011;
    wire op_system   = opcode == 5'b11100;

    wire funct7_zero = funct7 == 7'b0000000;
    wire funct7_alt  = funct7 == 7'b0100000;
    wire alu_add  = funct3 == 3'b000;
    wire alu_sl   = funct3 == 3'b001;
    wire alu_slt  = funct3 == 3'b010;
    wire alu_sltu = funct3 == 3'b011;
    wire alu_xor  = funct3 == 3'b100;
    wire alu_sr   = funct3 == 3'b101;
    wire alu_or   = funct3 == 3'b110;
    wire alu_and  = funct3 == 3'b111;

    wire beq  = funct3 == 3'b000;
    wire bne  = funct3 == 3'b001;
    wire blt  = funct3 == 3'b100;
    wire bge  = funct3 == 3'b101;
    wire bltu = funct3 == 3'b110;
    wire bgeu = funct3 == 3'b111;

    wire memb  = funct3 == 3'b000;
    wire memh  = funct3 == 3'b001;
    wire memw  = funct3 == 3'b010;
    wire membu = funct3 == 3'b100;
    wire memhu = funct3 == 3'b101;

    wire priv  = funct3 == 3'b000;

    // Disable source register reads for instructions that do not use them
    // for pipeline RAW hazard correctness (and power efficiency, technically).
    wire rs1_valid = op_load | op_op_imm | op_store | op_op | op_branch | op_jalr;
    wire rs2_valid = op_store | op_op | op_branch;

    // These specific instruction selects are needed for generating control
    // signals and to validate the instruction against illegal opcodes. It is
    // most likely possible to find more optimal ways to select these control
    // signals but this is straight forward and reasonably efficient. Not all
    // instructions are listed here as some opcodes do not have any illegal
    // encodings or are not needed to generate control signals. Some signals
    // select single instructions while others select groups.
    wire inst_sub       = op_op & alu_add & funct7_alt;
    wire inst_slt       = op_op & alu_slt & funct7_zero;
    wire inst_sltu      = op_op & alu_sltu & funct7_zero;
    wire inst_slti      = op_op_imm & alu_slt;
    wire inst_sltiu     = op_op_imm & alu_sltu;
    wire inst_op_op     = op_op & (funct7_zero | (alu_add & funct7_alt) | (alu_sr & funct7_alt));
    wire inst_op_op_imm = op_op_imm & ((alu_sl & funct7_zero) | (alu_sr & funct7_zero) | (alu_sr & funct7_alt) | ~(alu_sl | alu_sr));
    wire inst_lui       = op_lui;
    wire inst_auipc     = op_auipc;
    wire inst_load      = op_load & (memb | memh | memw | membu | memhu);
    wire inst_store     = op_store & (memb | memh | memw);
    wire inst_branch    = op_branch & (beq | bne | blt | bge | bltu | bgeu);
    wire inst_branchu   = op_branch & (bltu | bgeu);
    wire inst_jal       = op_jal;
    wire inst_jalr      = op_jalr;
    wire inst_ebreak    = op_system & priv & (i_inst[31:20] == 32'h001);

    // Validate instructions against illegal encodings.
    wire uncompressed = i_inst[1:0] == 2'b11;
    wire legal = uncompressed & (inst_op_op | inst_op_op_imm | inst_lui | inst_auipc | inst_load | inst_store | inst_branch | inst_jal | inst_jalr | inst_ebreak);

    wire format_r = op_op;
    wire format_i = op_op_imm | op_jalr | op_load;
    wire format_s = op_store;
    wire format_b = op_branch;
    wire format_u = op_lui | op_auipc;
    wire format_j = op_jal;

    // Immediate decoder.
    wire [ 5:0] format = {format_j, format_u, format_b, format_s, format_i, format_r};
    wire [31:0] immediate;
    imm imm (
        .i_inst(i_inst),
        .i_format(format),
        .o_immediate(immediate)
    );

    // Some instructions that calculate a PC-relative target address utilize
    // the ALU to do so. The exception is the branch instructions which use
    // the ALU for comparison and a separate adder for target calculation.
    wire op1_sel = op_auipc | op_jal;
    // Instructions that operate on a single register and immediate bypass the
    // second source register rs2 and use the immediate instead. However,
    // branch target calculations do not use this datapath and use a separate
    // adder instead, as the ALU is used for comparison.
    wire op2_sel = op_op_imm | op_load | op_store | op_auipc | op_jalr;

    // The ALU opsel is normally directly mapped from the funct3 field.
    // However, it is also used for branch comparison, where the opsel doesn't
    // matter - only the comparison outputs are used (so sub and unsigned are
    // needed). The auipc instruction and memory instructions also use the
    // ALU for target calculation so is hardcoded to addition.
    wire [2:0] alu_opsel    = (inst_auipc | inst_load | inst_store) ? 3'b000 : funct3;
    wire       inst_slta    = inst_slt | inst_sltu | inst_slti | inst_sltiu;
    wire       alu_sub      = inst_sub | inst_slta | inst_branch;
    wire       alu_unsigned = inst_sltu | inst_sltiu | inst_branchu;
    wire       alu_arith    = funct7_alt;

    // Used to determine if the instruction should conditionally or
    // unconditionally jump to a non-sequential address, respectively.
    wire branch = op_branch;
    wire jump   = op_jalr | op_jal;
    wire pc_sel = op_jalr;

    // The branch comparator is shared with the ALU, but a bit of
    // post-processing logic is needed to determine the branch condition.
    wire branch_equal    = ~funct3[2];
    wire branch_unsigned =  funct3[1];
    wire branch_invert   =  funct3[0];

    // Memory read and write enable signals are generated from opcodes.
    wire       dmem_ren   = inst_load;
    wire       dmem_wen   = inst_store;
    wire [1:0] dmem_align = {memw, memh | memhu | memw};

    // The register write data is multiplexed between the ALU result, the
    // immediate, incremented PC, and memory load.
    wire       rd_alu = inst_op_op | inst_op_op_imm | inst_auipc;
    wire       rd_imm = inst_lui;
    wire       rd_pci = inst_jal | inst_jalr;
    wire       rd_mem = inst_load;
    wire [3:0] rd_sel = {rd_mem, rd_pci, rd_imm, rd_alu};

    // Disable register write for the instructions that don't write.
    wire       rd_wen    = ~(inst_branch | inst_store);
    wire [4:0] rd_masked = rd_wen ? rd : 5'd0;

    assign o_legal           = legal;
    assign o_halt            = inst_ebreak;
    assign o_rs1             = rs1_valid ? rs1 : 5'd0;
    assign o_rs2             = rs2_valid ? rs2 : 5'd0;
    assign o_rd              = rd_masked;
    assign o_op1_sel         = op1_sel;
    assign o_op2_sel         = op2_sel;
    assign o_immediate       = immediate;
    assign o_alu_opsel       = alu_opsel;
    assign o_alu_sub         = alu_sub;
    assign o_alu_unsigned    = alu_unsigned;
    assign o_alu_arith       = alu_arith;
    assign o_branch          = branch;
    assign o_jump            = jump;
    assign o_branch_equal    = branch_equal;
    assign o_branch_unsigned = branch_unsigned;
    assign o_branch_invert   = branch_invert;
    assign o_dmem_ren        = dmem_ren;
    assign o_dmem_wen        = dmem_wen;
    assign o_dmem_align      = dmem_align;
    assign o_dmem_memb       = memb | membu;
    assign o_dmem_memh       = memh | memhu;
    assign o_dmem_memw       = memw;
    assign o_dmem_memu       = membu | memhu;
    assign o_rd_sel          = rd_sel;
    assign o_pc_sel          = pc_sel;
endmodule

// The immediate generator is responsible for decoding the 32-bit
// sign-extended immediate from the incoming instruction word. It is a purely
// combinational block that is expected to be embedded in the instruction
// decoder.
module imm (
    // Input instruction word. This is used to extract the relevant immediate
    // bits and assemble them into the final immediate.
    input  wire [31:0] i_inst,
    // Instruction format, determined by the instruction decoder based on the
    // opcode. This is one-hot encoded according to the following format:
    // [0] R-type
    // [1] I-type
    // [2] S-type
    // [3] B-type
    // [4] U-type
    // [5] J-type
    // Because the R-type format does not have an immediate, the output
    // immediate can be treated as a don't-care under this case.
    input  wire [ 5:0] i_format,
    // Output 32-bit immediate, sign-extended from the immediate bitstring.
    output wire [31:0] o_immediate
);
    // Reference implementation, do not distribute.

    wire format_i = i_format[1];
    wire format_s = i_format[2];
    wire format_b = i_format[3];
    wire format_u = i_format[4];
    wire format_j = i_format[5];

    wire format_sb = format_s | format_b;
    wire format_ij = format_i | format_j;
    wire format_uj = format_u | format_j;

    // The multiplexers have been split up by section of the immediate to
    // reduce area. Students are not expected to do this (but of course, are
    // encouraged to find such optimizations).
    wire [31:0] imm;
    assign imm[0] = (format_s & i_inst[7]) | (format_i & i_inst[20]);
    assign imm[4:1] = ({4{format_sb}} & i_inst[11:8]) | ({4{format_ij}} & i_inst[24:21]);
    assign imm[10:5] = {6{!format_u}} & i_inst[30:25];
    assign imm[11] = format_b ? i_inst[7] : (format_j ? i_inst[20] : (format_u ? 1'b0 : i_inst[31]));
    assign imm[19:12] = format_uj ? i_inst[19:12] : {8{i_inst[31]}};
    assign imm[30:20] = format_u ? i_inst[30:20] : {11{i_inst[31]}};
    assign imm[31] = i_inst[31];

    assign o_immediate = imm;
endmodule

`default_nettype wire
