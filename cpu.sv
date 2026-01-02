`timescale 1ns/10ps
// Gate level Single-Cycle CPU

// 2-to-1 mux for 3-bit vectors driven by two one-hot select bits (sel0 selects in0, sel1 selects in1)
module mux2_1_3(
    input  [2:0] in0,
    input  [2:0] in1,
    input        sel0,
    input        sel1,
    output [2:0] out
    );
    genvar i;
    generate
        for (i = 0; i < 3; i = i + 1) begin : gen2
            wire a0, a1;
            and2 and_l(.out(a0), .in0(in0[i]), .in1(sel0));
            and2 and_r(.out(a1), .in0(in1[i]), .in1(sel1));
            or2  or_out(.out(out[i]), .in0(a0), .in1(a1));
        end
    endgenerate
endmodule

// 4-to-1 mux for 3-bit vectors, driven by four one-hot select bits sel[0..3]
module mux4_1_3(
    input  [2:0] in_ [0:3],
    input  [3:0] sel,
    output [2:0] out
    );
    // first-level pairs
    wire [2:0] p0, p1;
    mux2_1_3 pair0(.in0(in_[0]), .in1(in_[1]), .sel0(sel[0]), .sel1(sel[1]), .out(p0));
    mux2_1_3 pair1(.in0(in_[2]), .in1(in_[3]), .sel0(sel[2]), .sel1(sel[3]), .out(p1));

    // compute group select signals
    wire g0sel, g1sel;
    or2 og0(.out(g0sel), .in0(sel[0]), .in1(sel[1]));
    or2 og1(.out(g1sel), .in0(sel[2]), .in1(sel[3]));

    // final choose between p0 and p1 using their signals
    mux2_1_3 final_pair(.in0(p0), .in1(p1), .sel0(g0sel), .sel1(g1sel), .out(out));
endmodule

// 2-to-1 mux for 5-bit vectors (for register address selection)
module mux2_1_5(
    input  [4:0] in0,
    input  [4:0] in1,
    input        sel,
    input        sel_n,
    output [4:0] out
    );
    genvar i;
    generate
        for (i = 0; i < 5; i = i + 1) begin : gen5
            wire a0, a1;
            and2 and_l(.out(a0), .in0(in0[i]), .in1(sel_n));
            and2 and_r(.out(a1), .in0(in1[i]), .in1(sel));
            or2  or_out(.out(out[i]), .in0(a0), .in1(a1));
        end
    endgenerate
endmodule

// Control unit: generate control signals from op_sel
module control_unit(
    input  [10:0] op_sel,
    output reg Reg2Loc,
    output reg ALUSrc,
    output reg MemToReg,
    output reg RegWrite,
    output reg MemWrite,
    output reg UncondBr,
    output reg Branch, // conditional branch
    output reg [2:0] ALUOp
    );
    // op_sel ordering: {is_subs, is_stur, is_lsr, is_ldur, is_eor, is_cbz, is_blt, is_b, is_and, is_adds, is_addi}
    wire is_subs = op_sel[10];
    wire is_stur = op_sel[9];
    wire is_lsr  = op_sel[8];
    wire is_ldur = op_sel[7];
    wire is_eor  = op_sel[6];
    wire is_cbz  = op_sel[5];
    wire is_blt  = op_sel[4];
    wire is_b    = op_sel[3];
    wire is_and  = op_sel[2];
    wire is_adds = op_sel[1];
    wire is_addi = op_sel[0];

    always @(*) begin
        // defaults
        Reg2Loc = 1'b1;
        ALUSrc = 1'b0;
        MemToReg = 1'b0;
        RegWrite = 1'b0;
        MemWrite = 1'b0;
        UncondBr = 1'b0;
        Branch = 1'b0;
        ALUOp = 3'b000;

        if (is_addi) begin
            ALUSrc = 1'b1;
            RegWrite = 1'b1;
            ALUOp = 3'b010; // add
        end else if (is_adds) begin
            RegWrite = 1'b1;
            ALUOp = 3'b010;
        end else if (is_and) begin
            RegWrite = 1'b1;
            ALUOp = 3'b100;
        end else if (is_subs) begin
            RegWrite = 1'b1;
            ALUOp = 3'b011;
        end else if (is_ldur) begin
            Reg2Loc = 1'b0;
            ALUSrc = 1'b1;
            MemToReg = 1'b1;
            RegWrite = 1'b1;
            ALUOp = 3'b010; // address add
        end else if (is_stur) begin
            Reg2Loc = 1'b0;
            ALUSrc = 1'b1;
            MemWrite = 1'b1;
            ALUOp = 3'b010;
        end else if (is_b) begin
            Reg2Loc = 1'b0;
            UncondBr = 1'b1;
        end else if (is_cbz) begin
            Reg2Loc = 1'b0;
            Branch = 1'b1; // conditional
        end else if (is_lsr) begin
            ALUSrc = 1'b1; // shamt treated as immediate
            RegWrite = 1'b1;
            ALUOp = 3'b001;
        end else if (is_eor) begin
            RegWrite = 1'b1;
            ALUOp = 3'b110;
        end else if (is_blt) begin
            Branch = 1'b1;
        end
    end
endmodule

// Instruction fetch stage: holds PC register and instruction memory
module instr_stage(
    input  clk,
    input  [63:0] pc_in,
    output [63:0] pc_out,
    output [31:0] instr,
    output [63:0] pc_plus4
    );
    reg64 pc_reg(.q(pc_out), .d(pc_in), .clk(clk), .enable(1'b1));
    instructmem imem(.address(pc_out), .instruction(instr), .clk(clk));
    adder64 pcadd(.in0(pc_out), .in1(64'd4), .cin(1'b0), .sum(pc_plus4), .cout());
endmodule

// Register file / decode stage: extract fields, read registers, and produce op_sel signals
module regfile_stage(
    input  clk,
    input  [31:0] instr,
    input  [63:0] write_data,
    output [63:0] rf_r1,
    output [63:0] rf_r2,
    output [4:0] rd, rn, rm,
    output [11:0] imm12,
    output [18:0] imm19,
    output [25:0] imm26,
    output [8:0] imm9,
    output [5:0] shamt,
    output [63:0] imm_selected,
    output [10:0] op_sel,
    // control outputs
    output Reg2Loc,
    output ALUSrc,
    output MemToReg,
    output RegWrite,
    output MemWrite,
    output UncondBr,
    output Branch,
    output [2:0] ALUOp
    );
    // buffers
    wire [31:0] instr_w;
    buf b0[31:0](instr_w, instr);
    buf b1[4:0](rd, instr_w[4:0]);
    buf b2[4:0](rn, instr_w[9:5]);
    buf b3[4:0](rm, instr_w[20:16]);
    buf b4[11:0](imm12, instr_w[21:10]);
    buf b5[18:0](imm19, instr_w[23:5]);
    buf b6[25:0](imm26, instr_w[25:0]);
    buf b7[8:0](imm9, instr_w[20:12]);
    buf b8[5:0](shamt, instr_w[15:10]);

    // control unit (decode)
    wire cu_Reg2Loc, cu_ALUSrc, cu_MemToReg, cu_RegWrite, cu_MemWrite, cu_UncondBr, cu_Branch;
    wire [2:0] cu_ALUOp;
    control_unit cu(.op_sel(op_sel), .Reg2Loc(cu_Reg2Loc), .ALUSrc(cu_ALUSrc), .MemToReg(cu_MemToReg), .RegWrite(cu_RegWrite), .MemWrite(cu_MemWrite), .UncondBr(cu_UncondBr), .Branch(cu_Branch), .ALUOp(cu_ALUOp));

    // select second read register depending on Reg2Loc (if 1 use Rm=instr[20:16], else use Rt=instr[4:0])
    wire [4:0] readReg2;
    wire cu_Reg2Loc_n;
    not1 n_reg2loc(.out(cu_Reg2Loc_n), .in0(cu_Reg2Loc));
    mux2_1_5 reg2_mux(.in0(instr_w[4:0]), .in1(instr_w[20:16]), .sel(cu_Reg2Loc), .sel_n(cu_Reg2Loc_n), .out(readReg2));

    // register file instance
    regfile rf(.ReadData1(rf_r1), .ReadData2(rf_r2), .WriteData(write_data),
        .ReadRegister1(rn), .ReadRegister2(readReg2), .WriteRegister(rd),
        .RegWrite(cu_RegWrite), .clk(clk));

    // export control signals
    assign Reg2Loc = cu_Reg2Loc;
    assign ALUSrc = cu_ALUSrc;
    assign MemToReg = cu_MemToReg;
    assign RegWrite = cu_RegWrite;
    assign MemWrite = cu_MemWrite;
    assign UncondBr = cu_UncondBr;
    assign Branch = cu_Branch;
    assign ALUOp = cu_ALUOp;

    // opcode slices
    wire [9:0] op10 = instr_w[31:22];
    wire [10:0] op11 = instr_w[31:21];
    wire [7:0] op8 = instr_w[31:24];
    wire [5:0] op6 = instr_w[31:26];
    // local opcode booleans
    wire is_addi = (op10 == 10'b1001000100);
    wire is_adds = (op11 == 11'b10101011000);
    wire is_and  = (op11 == 11'b10001010000);
    wire is_b    = (op6  == 6'b000101);
    wire is_blt  = (op8  == 8'b01010100);
    wire is_cbz  = (op8  == 8'b10110100);
    wire is_eor  = (op11 == 11'b11001010000);
    wire is_ldur = (op11 == 11'b11111000010);
    wire is_lsr  = (op11 == 11'b11010011010);
    wire is_stur = (op11 == 11'b11111000000);
    wire is_subs = (op11 == 11'b11101011000);

    assign op_sel = {is_subs, is_stur, is_lsr, is_ldur, is_eor, is_cbz, is_blt, is_b, is_and, is_adds, is_addi};

    // Produce a formatted 64-bit immediate
    // imm12: zero-extend 12-bit, imm9: sign-extend 9-bit, shamt: zero-extend 6-bit
    wire [63:0] imm64_addi = {{52'b0}, imm12};
    wire [63:0] imm64_ldst = {{55{imm9[8]}}, imm9};
    wire [63:0] imm64_shamt = {58'b0, shamt};
    
    // immediate selection
    // Mapping: input_[0]=ADDI, input_[1]=LDST, input_[2]=LSR, input_[3]=zero    
    wire sel_ldst;
    or2 or_ldst(.out(sel_ldst), .in0(is_ldur), .in1(is_stur));
  
    // sel[0] = is_ldur | is_stur, sel[1] = is_lsr
    // ADDI: sel=00, LDST: sel=01, LSR: sel=10, none: sel=11
    wire [1:0] imm_sel = {is_lsr, sel_ldst};
    wire [1:0] imm_sel_n;
    not1 n_sel0(.out(imm_sel_n[0]), .in0(imm_sel[0]));
    not1 n_sel1(.out(imm_sel_n[1]), .in0(imm_sel[1]));
    
    mux4_1_64 imm_mux(.input_({imm64_addi, imm64_ldst, imm64_shamt, 64'b0}), .sel(imm_sel), .sel_n(imm_sel_n), .out(imm_selected));
endmodule

// ALU stage: choose ALU control and inputs based on op_sel and produce ALU outputs
module alu_stage(
    input  [63:0] rf_r1,
    input  [63:0] rf_r2,
    input  [63:0] imm_selected,
    input  [10:0] op_sel,
    input  ALUSrc,
    input  [2:0] ALUOp,
    output [63:0] alu_out,
    output alu_neg, alu_zero, alu_ovf, alu_carry
    );
    // ALU control supplied by control unit
    wire [2:0] alu_ctrl = ALUOp;
    // ALU B selection (in0=rf_r2, in1=imm_selected)
    wire sel_n;
    not1 n_sel(.out(sel_n), .in0(ALUSrc));
    wire [63:0] alu_b;
    mux2_1_64 b_mux2(.in0(rf_r2), .in1(imm_selected), .sel(ALUSrc), .sel_n(sel_n), .out(alu_b));

    // ALU instance
    alu alu_inst(.A(rf_r1), .B(alu_b), .cntrl(alu_ctrl), .result(alu_out), .negative(alu_neg), .zero(alu_zero), .overflow(alu_ovf), .carry_out(alu_carry));
endmodule

// Memory stage: handle loads/stores
module mem_stage(
    input clk,
    input [63:0] alu_out,
    input [63:0] write_data_in,
    input mem_we,
    input mem_re,
    input [3:0] mem_size,
    output [63:0] mem_out
    );

    // data memory instance
    datamem dmem(.address(alu_out), .write_enable(mem_we), .read_enable(mem_re), .write_data(write_data_in), .clk(clk), .xfer_size(mem_size), .read_data(mem_out));
endmodule

// Writeback stage: choose writeback data, update flags, and compute next PC
module write_stage(
    input clk,
    input [63:0] pc_out,
    input [63:0] pc_plus4,
    input [63:0] alu_out,
    input [63:0] mem_out,
    input [63:0] rf_r2,
    input [10:0] op_sel,
    input [25:0] imm26,
    input [18:0] imm19,
    input [4:0] rd,
    input alu_neg, alu_zero, alu_ovf, alu_carry,
    input MemToReg,
    input UncondBr,
    input Branch,
    output [63:0] write_data,
    output [63:0] pc_next,
    output flag_neg_q, flag_zero_q, flag_ovf_q, flag_carry_q
    );
    // decode local op types from op_sel for branch decisions and flag updates
    wire is_addi = op_sel[0];
    wire is_adds = op_sel[1];
    wire is_and  = op_sel[2];
    wire is_b    = op_sel[3];
    wire is_blt  = op_sel[4];
    wire is_cbz  = op_sel[5];
    wire is_eor  = op_sel[6];
    wire is_ldur = op_sel[7];
    wire is_lsr  = op_sel[8];
    wire is_stur = op_sel[9];
    wire is_subs = op_sel[10];
    // writeback mux: choose between ALU result and Memory (MemToReg)
    wire sel_mem_n;
    not1 n_mem(.out(sel_mem_n), .in0(MemToReg));
    mux2_1_64 wb_mux(.in0(alu_out), .in1(mem_out), .sel(MemToReg), .sel_n(sel_mem_n), .out(write_data));

    // Branch targets
    // Sign-extend branch immediates after implicit <<2:
    // B:   26-bit imm -> (26+2)=28 bits, so replicate 64-28=36
    // CBZ/BLT: 19-bit imm -> (19+2)=21 bits, so replicate 64-21=43
    wire [63:0] b_offset   = {{36{imm26[25]}}, imm26, 2'b00};
    wire [63:0] cbz_offset = {{43{imm19[18]}}, imm19, 2'b00};
    wire [63:0] blt_offset = {{43{imm19[18]}}, imm19, 2'b00};
    wire [63:0] branch_target; wire [63:0] cbz_target; wire [63:0] blt_target;
    adder64 btarget(.in0(pc_out), .in1(b_offset), .cin(1'b0), .sum(branch_target), .cout());
    adder64 cbztarget(.in0(pc_out), .in1(cbz_offset), .cin(1'b0), .sum(cbz_target), .cout());
    adder64 blttarget(.in0(pc_out), .in1(blt_offset), .cin(1'b0), .sum(blt_target), .cout());

    // cbz cond: zero detect on rf_r2
    wire rf2_zero;
    zero_detect zd(.data(rf_r2), .zero(rf2_zero));

    // Flag registers to store ADDS/SUBS results
    // wire flag_neg_q, flag_zero_q, flag_ovf_q, flag_carry_q;
    
    // BLT cond: N != V ==> use stored flags from previous ADDS/SUBS
    wire blt_cond;
    xor2 xblt(.out(blt_cond), .in0(flag_neg_q), .in1(flag_ovf_q));

    // compute final pc_next with muxes (priority: B, CBZ, BLT)
    // if B -> branch_target, else if CBZ and rf1_zero -> cbz_target, else if BLT and blt_cond -> blt_target, else pc_plus4
    wire take_b = is_b;
    wire take_cbz;
    and2 and_cbz(.out(take_cbz), .in0(is_cbz), .in1(rf2_zero));
    wire take_blt;
    and2 and_blt(.out(take_blt), .in0(is_blt), .in1(blt_cond));

    // First level: choose between pc_plus4_local and blt_target if take_blt
    wire [63:0] level1;
    wire sel_blt_n; not1 n_blt(.out(sel_blt_n), .in0(take_blt));
    mux2_1_64 m_lvl1(.in0(pc_plus4), .in1(blt_target), .sel(take_blt), .sel_n(sel_blt_n), .out(level1));
    // level2: choose between level1 and cbz_target if take_cbz
    wire [63:0] level2;
    wire sel_cbz_n;
    not1 ncbz_n(.out(sel_cbz_n), .in0(take_cbz));
    mux2_1_64 m_lvl2(.in0(level1), .in1(cbz_target), .sel(take_cbz), .sel_n(sel_cbz_n), .out(level2));
    // final: choose between level2 and branch_target if take_b
    wire sel_b_n; not1 nb(.out(sel_b_n), .in0(take_b));
    mux2_1_64 m_lvl3(.in0(level2), .in1(branch_target), .sel(take_b), .sel_n(sel_b_n), .out(pc_next));

    // update flags (DFF) when ADDS or SUBS
    wire flag_en; or2 flagen(.out(flag_en), .in0(is_adds), .in1(is_subs));
    reg1 neg_flag(.q(flag_neg_q), .d(alu_neg), .clk(clk), .enable(flag_en));
    reg1 zero_flag(.q(flag_zero_q), .d(alu_zero), .clk(clk), .enable(flag_en));
    reg1 ovf_flag(.q(flag_ovf_q), .d(alu_ovf), .clk(clk), .enable(flag_en));
    reg1 carry_flag(.q(flag_carry_q), .d(alu_carry), .clk(clk), .enable(flag_en));
endmodule

// Top-level CPU wires and instantiation of the five stages
module cpu(
    input clk
    );
    // wires shared between stages
    wire [63:0] pc_in, pc_out, pc_plus4;
    wire [31:0] instr;
    wire [63:0] rf_r1, rf_r2;
    wire [4:0] rd, rn, rm;
    wire [11:0] imm12;
    wire [18:0] imm19;
    wire [25:0] imm26;
    wire [8:0] imm9;
    wire [5:0] shamt;
    wire [10:0] op_sel;
    wire [63:0] alu_out, mem_out, write_data;
    wire alu_neg, alu_zero, alu_ovf, alu_carry;
    wire [63:0] imm_selected;
    wire mem_we, mem_re;
    wire [3:0] mem_size;
    wire rf_we;

    // default mem size
    assign mem_size = 4'd8;

    instr_stage is0(.clk(clk), .pc_in(pc_in), .pc_out(pc_out), .instr(instr), .pc_plus4(pc_plus4));

    // instantiate control unit via regfile_stage outputs
    wire Reg2Loc, ALUSrc, MemToReg, RegWrite, MemWrite, UncondBr, Branch;
    wire [2:0] ALUOp;
    // regfile_stage now provides control outputs
    regfile_stage rfs(.clk(clk), .instr(instr), .write_data(write_data), .rf_r1(rf_r1), .rf_r2(rf_r2), .rd(rd), .rn(rn), .rm(rm), .imm12(imm12), .imm19(imm19), .imm26(imm26), .imm9(imm9), .shamt(shamt), .imm_selected(imm_selected), .op_sel(op_sel), .Reg2Loc(Reg2Loc), .ALUSrc(ALUSrc), .MemToReg(MemToReg), .RegWrite(RegWrite), .MemWrite(MemWrite), .UncondBr(UncondBr), .Branch(Branch), .ALUOp(ALUOp));

    alu_stage als(.rf_r1(rf_r1), .rf_r2(rf_r2), .imm_selected(imm_selected), .op_sel(op_sel), .ALUSrc(ALUSrc), .ALUOp(ALUOp), .alu_out(alu_out), .alu_neg(alu_neg), .alu_zero(alu_zero), .alu_ovf(alu_ovf), .alu_carry(alu_carry));

    // mem control signals come from control unit outputs
    assign mem_we = MemWrite;
    assign mem_re = MemToReg; // MemToReg indicates we need to read from memory for writeback (LDUR)
    mem_stage ms(.clk(clk), .alu_out(alu_out), .write_data_in(rf_r2), .mem_we(mem_we), .mem_re(mem_re), .mem_size(mem_size), .mem_out(mem_out));
    write_stage ws(.clk(clk), .pc_out(pc_out), .pc_plus4(pc_plus4), .alu_out(alu_out), .mem_out(mem_out), .rf_r2(rf_r2), .op_sel(op_sel), .imm26(imm26), .imm19(imm19), .rd(rd), .alu_neg(alu_neg), .alu_zero(alu_zero), .alu_ovf(alu_ovf), .alu_carry(alu_carry), .write_data(write_data), .pc_next(pc_in), .MemToReg(MemToReg), .UncondBr(UncondBr), .Branch(Branch), .flag_neg_q(), .flag_zero_q(), .flag_ovf_q(), .flag_carry_q());
endmodule
