`default_nettype none

module hart #(
    // After reset, the program counter (PC) should be initialized to this
    // address and start executing instructions from there.
    parameter RESET_ADDR = 32'h00000000
) (
    // Global clock.
    input  wire        i_clk,
    // Synchronous active-high reset.
    input  wire        i_rst,
    // Instruction fetch goes through a read only instruction memory (imem)
    // port. The port accepts a 32-bit address (e.g. from the program counter)
    // per cycle and combinationally returns a 32-bit instruction word. This
    // is not representative of a realistic memory interface; it has been
    // modeled as more similar to a DFF or SRAM to simplify phase 3. In
    // later phases, you will replace this with a more realistic memory.
    //
    // 32-bit read address for the instruction memory. This is expected to be
    // 4 byte aligned - that is, the two LSBs should be zero.
    output wire [31:0] o_imem_raddr,
    // Instruction word fetched from memory, available on the same cycle.
    input  wire [31:0] i_imem_rdata,
    // Data memory accesses go through a separate read/write data memory (dmem)
    // that is shared between read (load) and write (stored). The port accepts
    // a 32-bit address, read or write enable, and mask (explained below) each
    // cycle. Reads are combinational - values are available immediately after
    // updating the address and asserting read enable. Writes occur on (and
    // are visible at) the next clock edge.
    //
    // Read/write address for the data memory. This should be 32-bit aligned
    // (i.e. the two LSB should be zero). See `o_dmem_mask` for how to perform
    // half-word and byte accesses at unaligned addresses.
    output wire [31:0] o_dmem_addr,
    // When asserted, the memory will perform a read at the aligned address
    // specified by `i_addr` and return the 32-bit word at that address
    // immediately (i.e. combinationally). It is illegal to assert this and
    // `o_dmem_wen` on the same cycle.
    output wire        o_dmem_ren,
    // When asserted, the memory will perform a write to the aligned address
    // `o_dmem_addr`. When asserted, the memory will write the bytes in
    // `o_dmem_wdata` (specified by the mask) to memory at the specified
    // address on the next rising clock edge. It is illegal to assert this and
    // `o_dmem_ren` on the same cycle.
    output wire        o_dmem_wen,
    // The 32-bit word to write to memory when `o_dmem_wen` is asserted. When
    // write enable is asserted, the byte lanes specified by the mask will be
    // written to the memory word at the aligned address at the next rising
    // clock edge. The other byte lanes of the word will be unaffected.
    output wire [31:0] o_dmem_wdata,
    // The dmem interface expects word (32 bit) aligned addresses. However,
    // WISC-25 supports byte and half-word loads and stores at unaligned and
    // 16-bit aligned addresses, respectively. To support this, the access
    // mask specifies which bytes within the 32-bit word are actually read
    // from or written to memory.
    //
    // To perform a half-word read at address 0x00001002, align `o_dmem_addr`
    // to 0x00001000, assert `o_dmem_ren`, and set the mask to 0b1100 to
    // indicate that only the upper two bytes should be read. Only the upper
    // two bytes of `i_dmem_rdata` can be assumed to have valid data; to
    // calculate the final value of the `lh[u]` instruction, shift the rdata
    // word right by 16 bits and sign/zero extend as appropriate.
    //
    // To perform a byte write at address 0x00002003, align `o_dmem_addr` to
    // `0x00002003`, assert `o_dmem_wen`, and set the mask to 0b1000 to
    // indicate that only the upper byte should be written. On the next clock
    // cycle, the upper byte of `o_dmem_wdata` will be written to memory, with
    // the other three bytes of the aligned word unaffected. Remember to shift
    // the value of the `sb` instruction left by 24 bits to place it in the
    // appropriate byte lane.
    output wire [ 3:0] o_dmem_mask,
    // The 32-bit word read from data memory. When `o_dmem_ren` is asserted,
    // this will immediately reflect the contents of memory at the specified
    // address, for the bytes enabled by the mask. When read enable is not
    // asserted, or for bytes not set in the mask, the value is undefined.
    input  wire [31:0] i_dmem_rdata,
    // The output `retire` interface is used to signal to the testbench that
    // the CPU has completed and retired an instruction. A single cycle
    // implementation will assert this every cycle; however, a pipelined
    // implementation that needs to stall (due to internal hazards or waiting
    // on memory accesses) will not assert the signal on cycles where the
    // instruction in the writeback stage is not retiring.
    //
    // Asserted when an instruction is being retired this cycle. If this is
    // not asserted, the other retire signals are ignored and may be left invalid.
    output wire        o_retire_valid,
    // The 32 bit instruction word of the instrution being retired. This
    // should be the unmodified instruction word fetched from instruction
    // memory.
    output wire [31:0] o_retire_inst,
    // Asserted if the instruction produced a trap, due to an illegal
    // instruction, unaligned data memory access, or unaligned instruction
    // address on a taken branch or jump.
    output wire        o_retire_trap,
    // Asserted if the instruction is an `ebreak` instruction used to halt the
    // processor. This is used for debugging and testing purposes to end
    // a program.
    output wire        o_retire_halt,
    // The first register address read by the instruction being retired. If
    // the instruction does not read from a register (like `lui`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs1_raddr,
    // The second register address read by the instruction being retired. If
    // the instruction does not read from a second register (like `addi`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs2_raddr,
    // The first source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs1 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs1_rdata,
    // The second source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs2 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs2_rdata,
    // The destination register address written by the instruction being
    // retired. If the instruction does not write to a register (like `sw`),
    // this should be 5'd0.
    output wire [ 4:0] o_retire_rd_waddr,
    // The destination register data written to the register file in the
    // writeback stage by this instruction. If rd is 5'd0, this field is
    // ignored and can be treated as a don't care.
    output wire [31:0] o_retire_rd_wdata,
    output wire [31:0] o_retire_dmem_addr,
    output wire [ 3:0] o_retire_dmem_mask,
    output wire        o_retire_dmem_ren,
    output wire        o_retire_dmem_wen,
    output wire [31:0] o_retire_dmem_rdata,
    output wire [31:0] o_retire_dmem_wdata,
    // The current program counter of the instruction being retired - i.e.
    // the instruction memory address that the instruction was fetched from.
    output wire [31:0] o_retire_pc,
    // the next program counter after the instruction is retired. For most
    // instructions, this is `o_retire_pc + 4`, but must be the branch or jump
    // target for *taken* branches and jumps.
    output wire [31:0] o_retire_next_pc

`ifdef RISCV_FORMAL
    ,`RVFI_OUTPUTS,
`endif
);
    // Reference implementation, do not distribute.

    // This is the source of truth for the program counter (PC). The PC is
    // updated on every cycle, either by incrementing by 4 or j umping to
    // a new address for branches or jumps. As branch prediction is not
    // currently enabled, the fetch stage stalls any time there is a control
    // hazard.
    // Because this is a single cycle implementation, there is a single source
    // of truth for the program counter (PC). The PC is updated on every cycle,
    // either by incrementing by 4 or jumping to a new address for branches or
    // jumps. The next PC is also used to read from instruction memory.
    reg  [31:0] pc;
    wire [31:0] next_pc;
    wire        stall;
    always @(posedge i_clk) begin
        if (i_rst)
            pc <= RESET_ADDR;
        else
            pc <= next_pc;
    end

    // Each cycle, the PC can advance to one of the following:
    // * PC + 4 (normal instruction flow)
    // * PC (stall due to data or control hazard, or halted)
    // * Jump target (taken branch or jump)
    //
    // Increment PC has no control dependencies.
    wire [31:0] pc_increment = pc + 32'd4;
    // Jump target and taken/not taken are calculated in the execute stage.
    wire [31:0] pc_jump;
    wire        taken;
    assign next_pc = taken ? pc_jump : stall ? pc : pc_increment;

    // Sticky halt register, triggered by ebreak and traps.
    // Requires reset to clear.
    reg halted;
    wire halt;
    always @(posedge i_clk) begin
        if (i_rst)
            halted <= 1'b0;
        else
            halted <= halt;
    end

    // Sticky delay register, accounts for instruction memory being invalid for
    // the first cycle after reset.
    reg imem_valid;
    always @(posedge i_clk) begin
        if (i_rst)
            imem_valid <= 1'b0;
        else
            imem_valid <= 1'b1;
    end

    // Read from the instruction memory at the next PC address, which will
    // arrive after the clock in time to be used in the next cycle.
    assign o_imem_raddr = next_pc;
    wire [31:0] pd_inst = i_imem_rdata;

    // Pre-decode the instruction in the IF stage to check the source
    // registers. If either of them introduces a data hazard, insert a stall
    // (bubble) into the decode stage. Check the opcode first to see if the
    // instruction actually uses either source register.
    wire [ 4:0] pd_opcode    = pd_inst[6:2];
    wire        pd_op_load   = pd_opcode == 5'b00000;
    wire        pd_op_op_imm = pd_opcode == 5'b00100;
    wire        pd_op_auipc  = pd_opcode == 5'b00101;
    wire        pd_op_store  = pd_opcode == 5'b01000;
    wire        pd_op_op     = pd_opcode == 5'b01100;
    wire        pd_op_lui    = pd_opcode == 5'b01101;
    wire        pd_op_branch = pd_opcode == 5'b11000;
    wire        pd_op_jalr   = pd_opcode == 5'b11001;
    wire        pd_op_jal    = pd_opcode == 5'b11011;
    wire        pd_op_system = pd_opcode == 5'b11100;

    wire        pd_rs1_valid = pd_op_load | pd_op_op_imm | pd_op_store | pd_op_op | pd_op_branch | pd_op_jalr;
    wire        pd_rs2_valid = pd_op_store | pd_op_op | pd_op_branch;
    wire [ 4:0] pd_rs1_addr = pd_rs1_valid ? pd_inst[19:15] : 5'd0;
    wire [ 4:0] pd_rs2_addr = pd_rs2_valid ? pd_inst[24:20] : 5'd0;

    // RAW data hazard if the source register the destination register in any
    // of the downstream stages.
    wire rs1_exex   = (pd_rs1_addr != 5'd0) & if_valid & ~dmem_ren & (pd_rs1_addr == rd_addr);
    // wire rs1_memex  = (pd_rs1_addr != 5'd0) & id_valid & ~if_rs1_exex & (pd_rs1_addr == id_rd_addr);
    wire rs1_memex  = (pd_rs1_addr != 5'd0) & id_valid & (pd_rs1_addr != rd_addr) & (pd_rs1_addr == id_rd_addr);
    wire rs1_hazard = (pd_rs1_addr != 5'd0) & if_valid & dmem_ren & (pd_rs1_addr == rd_addr);
    wire rs2_exex   = (pd_rs2_addr != 5'd0) & if_valid & ~dmem_ren & (pd_rs2_addr == rd_addr);
    wire rs2_memex  = (pd_rs2_addr != 5'd0) & id_valid & (pd_rs2_addr != rd_addr) & (pd_rs2_addr == id_rd_addr);
    wire rs2_hazard = (pd_rs2_addr != 5'd0) & if_valid & dmem_ren & (pd_rs2_addr == rd_addr);
    // Control hazard if the current instruction in the decode or execute
    // stages is a branch or jump.
    wire   ctrl_hazard = 1'b0;
    assign stall       = rs1_hazard | rs2_hazard | ctrl_hazard | halt | ~imem_valid;

    // Insert a pipeline bubble (nop) if there is a data hazard.
    wire [31:0] nop  = 32'h00000013;
    wire [31:0] inst = stall ? nop : pd_inst;

    // Instruction fetch pipeline barrier.
    reg [31:0] if_inst;
    reg [31:0] if_pc, if_next_pc, if_pc_increment;
    reg        if_rs1_exex, if_rs2_exex;
    reg        if_rs1_memex, if_rs2_memex;
    always @(posedge i_clk) begin
        if_inst         <= inst;
        if_pc           <= pc;
        if_next_pc      <= next_pc;
        if_pc_increment <= pc_increment;
        if_rs1_exex     <= rs1_exex;
        if_rs2_exex     <= rs2_exex;
        if_rs1_memex    <= rs1_memex;
        if_rs2_memex    <= rs2_memex;
    end

    reg if_valid;
    always @(posedge i_clk) begin
        if (i_rst)
            if_valid <= 1'b0;
        else
            if_valid <= ~stall & ~taken;
    end

    // The register file is effectively an SRAM with two read ports and
    // 1 write port. It is read from here based on the instruction decoder
    // output (source registers) and written to in the writeback stage.
    wire [ 4:0] rs1_addr, rs2_addr, rd_addr;
    wire [31:0] rs1_rdata, rs2_rdata;
    reg  [31:0] rd_wdata;
    rf #(.BYPASS_EN(1)) rf (
        .i_clk       (i_clk    ),
        .i_rst       (i_rst    ),
        .i_rs1_raddr (rs1_addr ),
        .o_rs1_rdata (rs1_rdata),
        .i_rs2_raddr (rs2_addr ),
        .o_rs2_rdata (rs2_rdata),
        .i_rd_waddr  (mem_rd_addr  ),
        .i_rd_wdata  (rd_wdata )
    );

    // The instruction decoder is responsible for decoding the source
    // registers and immediate as well as generating control signals.
    wire        legal, ebreak;
    wire [31:0] immediate;
    wire        op1_sel, op2_sel;
    wire [ 2:0] alu_opsel;
    wire        alu_sub, alu_unsigned, alu_arith;
    wire        branch, jump;
    wire        branch_equal, branch_unsigned, branch_invert;
    wire        dmem_ren, dmem_wen;
    wire [ 1:0] dmem_align;
    wire        dmem_memb, dmem_memh, dmem_memw, dmem_memu;
    wire [ 3:0] rd_sel;
    wire        pc_sel;
    decoder decoder (
        .i_inst(if_inst),
        .o_legal(legal),
        .o_halt(ebreak),
        .o_rs1(rs1_addr),
        .o_rs2(rs2_addr),
        .o_rd(rd_addr),
        .o_op1_sel(op1_sel),
        .o_op2_sel(op2_sel),
        .o_immediate(immediate),
        .o_alu_opsel(alu_opsel),
        .o_alu_sub(alu_sub),
        .o_alu_unsigned(alu_unsigned),
        .o_alu_arith(alu_arith),
        .o_branch(branch),
        .o_jump(jump),
        .o_branch_equal(branch_equal),
        .o_branch_unsigned(branch_unsigned),
        .o_branch_invert(branch_invert),
        .o_dmem_ren(dmem_ren),
        .o_dmem_wen(dmem_wen),
        .o_dmem_align(dmem_align),
        .o_dmem_memb(dmem_memb),
        .o_dmem_memh(dmem_memh),
        .o_dmem_memw(dmem_memw),
        .o_dmem_memu(dmem_memu),
        .o_rd_sel(rd_sel),
        .o_pc_sel(pc_sel)
    );

    // Instruction decode pipeline barrier.
    reg [31:0] id_pc, id_next_pc, id_pc_increment;
    reg        id_rs1_exex, id_rs2_exex;
    reg        id_rs1_memex, id_rs2_memex;
    reg [ 4:0] id_rs1_addr, id_rs2_addr, id_rd_addr;
    reg [31:0] id_rs1_rdata, id_rs2_rdata;
    reg        id_legal, id_ebreak;
    reg [31:0] id_immediate;
    reg        id_op1_sel, id_op2_sel;
    reg [ 2:0] id_alu_opsel;
    reg        id_alu_sub, id_alu_unsigned, id_alu_arith;
    reg        id_branch, id_jump;
    reg        id_branch_equal, id_branch_unsigned, id_branch_invert;
    reg        id_dmem_ren, id_dmem_wen;
    reg [ 1:0] id_dmem_align;
    reg        id_dmem_memb, id_dmem_memh, id_dmem_memw, id_dmem_memu;
    reg [ 3:0] id_rd_sel;
    reg        id_pc_sel;
    always @(posedge i_clk) begin
        id_pc        <= if_pc;
        id_next_pc   <= if_next_pc;
        id_pc_increment <= if_pc_increment;
        id_rs1_exex  <= if_rs1_exex;
        id_rs2_exex  <= if_rs2_exex;
        id_rs1_memex <= if_rs1_memex;
        id_rs2_memex <= if_rs2_memex;
        id_rs1_addr  <= rs1_addr;
        id_rs2_addr  <= rs2_addr;
        id_rd_addr   <= rd_addr;
        id_rs1_rdata <= rs1_rdata;
        id_rs2_rdata <= rs2_rdata;
        id_legal     <= legal;
        id_ebreak    <= ebreak;
        id_immediate <= immediate;
        id_op1_sel   <= op1_sel;
        id_op2_sel   <= op2_sel;
        id_alu_opsel    <= alu_opsel;
        id_alu_sub      <= alu_sub;
        id_alu_unsigned <= alu_unsigned;
        id_alu_arith    <= alu_arith;
        id_branch    <= branch;
        id_jump      <= jump;
        id_branch_equal    <= branch_equal;
        id_branch_unsigned <= branch_unsigned;
        id_branch_invert   <= branch_invert;
        id_dmem_ren   <= dmem_ren;
        id_dmem_wen   <= dmem_wen;
        id_dmem_align <= dmem_align;
        id_dmem_memb  <= dmem_memb;
        id_dmem_memh  <= dmem_memh;
        id_dmem_memw  <= dmem_memw;
        id_dmem_memu  <= dmem_memu;
        id_rd_sel     <= rd_sel;
        id_pc_sel     <= pc_sel;
    end

    // Instruction decode pipeline barrier, debug harness only values.
    reg        id_valid;
    reg [31:0] id_inst;
    always @(posedge i_clk) begin
        if (i_rst)
            id_valid <= 1'b0;
        else
            id_valid <= if_valid & ~taken;

        id_inst <= if_inst;
    end

    // EX -> EX and MEM -> EX pipeline forwarding.
    reg [31:0] id_rs1_fwd, id_rs2_fwd;
    reg [31:0] ex_rd_wdata;
    always @(*) begin
        ex_rd_wdata = 32'hx;

        case (1'b1)
            ex_rd_sel[0]: ex_rd_wdata = ex_alu_result;
            ex_rd_sel[1]: ex_rd_wdata = ex_immediate;
            ex_rd_sel[2]: ex_rd_wdata = ex_pc_increment;
            // Data not available for forwarding.
            ex_rd_sel[3]: ex_rd_wdata = 32'hx;
        endcase
    end

    always @(*) begin
        id_rs1_fwd = 32'hx;
        id_rs2_fwd = 32'hx;

        if (id_rs1_exex)
            id_rs1_fwd = ex_rd_wdata;
        else if (id_rs1_memex)
            id_rs1_fwd = rd_wdata;
        else
            id_rs1_fwd = id_rs1_rdata;

        if (id_rs2_exex)
            id_rs2_fwd = ex_rd_wdata;
        else if (id_rs2_memex)
            id_rs2_fwd = rd_wdata;
        else
            id_rs2_fwd = id_rs2_rdata;
    end

    // The ALU is the core unit in this datapath and performs almost all
    // arithmetic operations including branch comparisons. The only exceptions
    // are the adders required for branch target calculation and PC increment.
    wire [31:0] alu_op1 = id_op1_sel ? id_pc        : id_rs1_fwd;
    wire [31:0] alu_op2 = id_op2_sel ? id_immediate : id_rs2_fwd;
    wire [31:0] alu_result;
    wire        eq, slt;
    alu alu (
        .i_opsel(id_alu_opsel),
        .i_sub(id_alu_sub),
        .i_unsigned(id_alu_unsigned),
        .i_arith(id_alu_arith),
        .i_op1(alu_op1),
        .i_op2(alu_op2),
        .o_result(alu_result),
        .o_eq(eq),
        .o_slt(slt)
    );

    // Branch comparison is done by the ALU but the result needs to be
    // combined to determine if the branch should be taken, which is also done
    // in the "EX" stage.
    wire   cond  = (id_branch_equal ? eq : slt) ^ id_branch_invert;
    assign taken = id_valid & ((id_branch & cond) | id_jump);

    wire [31:0] dmem_addr = alu_result;
    wire [ 1:0] dmem_lsb  = dmem_addr[1:0];
    wire [31:0] dmem_addr_aligned = {dmem_addr[31:2], 2'b00};

    wire [31:0] dmem_wdataw = id_rs2_fwd;
    wire [31:0] dmem_wdatah = dmem_lsb[1] ? {dmem_wdataw[15:0], 16'h0} : dmem_wdataw;
    wire [31:0] dmem_wdatab = dmem_lsb[0] ? {dmem_wdatah[24:0],  8'h0} : dmem_wdatah;
    wire [31:0] dmem_wdata  = dmem_wdatab;

    wire half0 = id_dmem_memh & ~dmem_lsb[1];
    wire half1 = id_dmem_memh &  dmem_lsb[1];
    wire byte0 = id_dmem_memb & ~dmem_lsb[1] & ~dmem_lsb[0];
    wire byte1 = id_dmem_memb & ~dmem_lsb[1] &  dmem_lsb[0];
    wire byte2 = id_dmem_memb &  dmem_lsb[1] & ~dmem_lsb[0];
    wire byte3 = id_dmem_memb &  dmem_lsb[1] &  dmem_lsb[0];

    wire [ 3:0] dmem_mask;
    assign dmem_mask[3] = id_dmem_memw | half1 | byte3;
    assign dmem_mask[2] = id_dmem_memw | half1 | byte2;
    assign dmem_mask[1] = id_dmem_memw | half0 | byte1;
    assign dmem_mask[0] = id_dmem_memw | half0 | byte0;

    assign o_dmem_addr  = dmem_addr_aligned;
    assign o_dmem_ren   = id_valid & id_dmem_ren;
    assign o_dmem_wen   = id_valid & id_dmem_wen;
    assign o_dmem_wdata = dmem_wdata;
    assign o_dmem_mask  = dmem_mask;

    // Calculate targets for branches and jumps.
    wire [31:0] branch_target = id_pc + id_immediate;
    wire [31:0] jalr_target   = {alu_result[31:1], 1'b0};
    assign      pc_jump       = id_pc_sel ? jalr_target : branch_target;

    // If branching or jumping, swap in the resolved target PC in the formal
    // interface.
    wire [31:0] resolved_next_pc = taken ? pc_jump : id_next_pc;

    // Trap conditions:
    // * Illegal instruction
    // * PC not 4 byte aligned
    // * Memory access not aligned
    wire pc_aligned  = resolved_next_pc[1:0] == 2'b00;
    // dmem_en -> aligned (implication)
    wire dmem_en = id_dmem_ren | id_dmem_wen;
    wire dmem_aligned = ~dmem_en | ((dmem_lsb & id_dmem_align) == 2'b00);
    // !rst & valid -> legal & pc_aligned & mem_aligned (implication)
    wire trap        = ~i_rst & id_valid & (~id_legal | ~pc_aligned | ~dmem_aligned);
    wire inst_break  = id_valid & id_legal & id_ebreak;

    assign halt      = halted | trap | inst_break;

    // Execute pipeline barrier. Memory reads and writes also happen at this
    // clock cycle, but are effectively "externally" registered.
    reg [31:0] ex_pc, ex_next_pc, ex_pc_increment;
    reg        ex_legal, ex_ebreak;
    reg [31:0] ex_immediate;
    reg        ex_dmem_ren, ex_dmem_wen;
    reg [ 1:0] ex_dmem_align;
    reg        ex_dmem_memw, ex_dmem_memh, ex_dmem_memu;
    reg [ 3:0] ex_rd_sel;
    reg        ex_pc_sel;
    reg [31:0] ex_alu_result;
    reg        ex_eq, ex_slt;
    reg        ex_cond;
    reg [ 1:0] ex_dmem_lsb;
    reg        ex_halt;
    always @(posedge i_clk) begin
        ex_pc         <= id_pc;
        ex_next_pc    <= resolved_next_pc;
        ex_pc_increment <= id_pc_increment;
        ex_legal      <= id_legal;
        ex_ebreak     <= id_ebreak;
        ex_immediate  <= id_immediate;
        ex_dmem_ren   <= id_dmem_ren;
        ex_dmem_wen   <= id_dmem_wen;
        ex_dmem_align <= id_dmem_align;
        ex_dmem_memw  <= id_dmem_memw;
        ex_dmem_memh  <= id_dmem_memh;
        ex_dmem_memu  <= id_dmem_memu;
        ex_rd_sel     <= id_rd_sel;
        ex_pc_sel     <= id_pc_sel;
        ex_alu_result <= alu_result;
        ex_eq         <= eq;
        ex_slt        <= slt;
        ex_cond       <= cond;
        ex_dmem_lsb   <= dmem_lsb;
        ex_halt       <= halt;
    end

    // Execute stage pipeline barrier, debug harness only values.
    reg        ex_valid;
    reg [31:0] ex_inst;
    reg        ex_trap;
    reg [ 4:0] ex_rs1_addr, ex_rs2_addr, ex_rd_addr;
    reg [31:0] ex_rs1_rdata, ex_rs2_rdata;
    reg [31:0] ex_dmem_addr;
    reg [31:0] ex_dmem_wdata;
    reg [ 3:0] ex_dmem_mask;
    always @(posedge i_clk) begin
        if (i_rst)
            ex_valid <= 1'b0;
        else
            ex_valid <= id_valid;

        ex_inst       <= id_inst;
        ex_trap       <= trap;
        ex_rs1_addr   <= id_rs1_addr;
        ex_rs2_addr   <= id_rs2_addr;
        ex_rd_addr    <= id_rd_addr;
        ex_rs1_rdata  <= id_rs1_fwd;
        ex_rs2_rdata  <= id_rs2_fwd;
        ex_dmem_addr  <= dmem_addr_aligned;
        ex_dmem_wdata <= dmem_wdata;
        ex_dmem_mask  <= dmem_mask;
    end

    wire [31:0] dmem_rdataw = i_dmem_rdata;
    wire [31:0] dmem_rdatah = ex_dmem_lsb[1] ? {16'h0, dmem_rdataw[31:16]} : dmem_rdataw;
    wire [31:0] dmem_rdatab = ex_dmem_lsb[0] ? { 8'h0, dmem_rdatah[31: 8]} : dmem_rdatah;

    wire        dmem_sign     = ex_dmem_memw ? dmem_rdataw[31] :
                                ex_dmem_memh ? dmem_rdatah[15] :
                                               dmem_rdatab[ 7];
    wire [31:0] dmem_ext_mask = {{16{ex_dmem_memw}}, {8{ex_dmem_memh | ex_dmem_memw}}, 8'hff};
    wire [31:0] dmem_sext     = {{32{dmem_sign & ~ex_dmem_memu}}};
    wire [31:0] dmem_rdata    = (dmem_rdatab & dmem_ext_mask) | (dmem_sext & ~dmem_ext_mask);

    // Memory stage pipeline barrier.
    reg [31:0] mem_pc, mem_next_pc, mem_pc_increment;
    reg        mem_legal, mem_ebreak;
    reg [31:0] mem_immediate;
    reg [31:0] mem_alu_result;
    reg [ 3:0] mem_rd_sel;
    reg        mem_pc_sel;
    reg [31:0] mem_dmem_rdata;
    reg        mem_halt;
    always @(posedge i_clk) begin
        mem_pc          <= ex_pc;
        mem_next_pc     <= ex_next_pc;
        mem_pc_increment <= ex_pc_increment;
        mem_legal       <= ex_legal;
        mem_ebreak      <= ex_ebreak;
        mem_immediate   <= ex_immediate;
        mem_alu_result  <= ex_alu_result;
        mem_rd_sel      <= ex_rd_sel;
        mem_pc_sel      <= ex_pc_sel;
        mem_dmem_rdata  <= dmem_rdata;
        mem_halt        <= ex_halt;
    end

    // Memory stage pipeline barrier, debug harness only values.
    reg        mem_valid;
    reg [31:0] mem_inst;
    reg        mem_trap;
    reg [ 4:0] mem_rs1_addr, mem_rs2_addr;
    reg [31:0] mem_rs1_rdata, mem_rs2_rdata;
    reg [ 4:0] mem_rd_addr;
    reg [31:0] mem_dmem_addr;
    reg [31:0] mem_dmem_wdata;
    reg        mem_dmem_ren, mem_dmem_wen;
    reg [ 3:0] mem_dmem_mask;
    reg [31:0] mem_rvfi_dmem_rdata;
    // FIXME: clean these up for synthesis
    always @(posedge i_clk) begin
        if (i_rst)
            mem_valid <= 1'b0;
        else
            mem_valid <= ex_valid;

        if (i_rst)
            mem_rd_addr <= 5'd0;
        else
            mem_rd_addr <= ex_valid ? ex_rd_addr : 5'd0;

        mem_inst       <= ex_inst;
        mem_trap       <= ex_trap;
        mem_rs1_addr   <= ex_rs1_addr;
        mem_rs2_addr   <= ex_rs2_addr;
        mem_rs1_rdata  <= ex_rs1_rdata;
        mem_rs2_rdata  <= ex_rs2_rdata;
        mem_dmem_addr  <= ex_dmem_addr;
        mem_dmem_wdata <= ex_dmem_wdata;
        mem_dmem_ren   <= ex_dmem_ren;
        mem_dmem_wen   <= ex_dmem_wen;
        mem_dmem_mask  <= ex_dmem_mask;
        mem_rvfi_dmem_rdata <= i_dmem_rdata;
    end

    always @(*) begin
        rd_wdata = 32'hx;

        case (1'b1)
            mem_rd_sel[0]: rd_wdata = mem_alu_result;
            mem_rd_sel[1]: rd_wdata = mem_immediate;
            mem_rd_sel[2]: rd_wdata = mem_pc_increment;
            mem_rd_sel[3]: rd_wdata = mem_dmem_rdata;
        endcase
    end

    assign o_retire_valid = ~i_rst & mem_valid;
    assign o_retire_inst  = mem_inst;
    assign o_retire_trap  = mem_trap;
    assign o_retire_halt  = mem_halt;

    assign o_retire_rs1_raddr = mem_rs1_addr;
    assign o_retire_rs2_raddr = mem_rs2_addr;
    assign o_retire_rs1_rdata = mem_rs1_rdata;
    assign o_retire_rs2_rdata = mem_rs2_rdata;

    assign o_retire_rd_waddr = mem_rd_addr;
    assign o_retire_rd_wdata = rd_wdata;

    assign o_retire_dmem_addr  = mem_dmem_addr;
    assign o_retire_dmem_mask  = mem_dmem_mask;
    assign o_retire_dmem_ren   = mem_dmem_ren;
    assign o_retire_dmem_wen   = mem_dmem_wen;
    assign o_retire_dmem_rdata = mem_rvfi_dmem_rdata;
    assign o_retire_dmem_wdata = mem_dmem_wdata;

    assign o_retire_pc       = mem_pc;
    assign o_retire_next_pc  = next_pc;

`ifdef RISCV_FORMAL
    reg  [63:0] rvfm_order;
    always @(posedge i_clk) begin
        if (i_rst)
            rvfm_order <= 64'h0;
        else
            rvfm_order <= rvfm_order + 64'h1;
    end

    assign rvfi_valid = ~i_rst & mem_valid & ~halt;
    assign rvfi_order = rvfm_order;
    assign rvfi_insn  = mem_inst;
    assign rvfi_trap  = mem_trap;
    assign rvfi_halt  = halt;
    assign rvfi_intr  = 1'b0;
    assign rvfi_mode  = 2'd3; // M-mode
    assign rvfi_ixl   = 2'd1; // XLEN = 32

    assign rvfi_rs1_addr  = mem_rs1_addr;
    assign rvfi_rs2_addr  = mem_rs2_addr;
    assign rvfi_rs1_rdata = mem_rs1_rdata;
    assign rvfi_rs2_rdata = mem_rs2_rdata;

    assign rvfi_rd_addr  = mem_rd_addr;
    assign rvfi_rd_wdata = (mem_rd_addr == 5'd0) ? 32'h0 : rd_wdata;

    assign rvfi_pc_rdata = mem_pc;
    assign rvfi_pc_wdata = mem_next_pc;

    assign rvfi_mem_addr  = mem_dmem_addr;
    assign rvfi_mem_rmask = mem_dmem_mask & {4{mem_dmem_ren}};
    assign rvfi_mem_wmask = mem_dmem_mask & {4{mem_dmem_wen}};
    assign rvfi_mem_rdata = mem_rvfi_dmem_rdata;
    assign rvfi_mem_wdata = mem_dmem_wdata;
`endif
endmodule

`default_nettype wire
