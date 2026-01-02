`timescale 1ns/10ps
// Pipelined 64-bit ARM-like CPU (IF/ID/EX/MEM/WB)
// Gate-level datapath with pipeline registers between stages

// N-bit register (built from reg1)
module regN #(parameter N = 5)(output [N-1:0] q, input [N-1:0] d, input clk, input enable);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : bits
            reg1 r(.q(q[i]), .d(d[i]), .clk(clk), .enable(enable));
        end
    endgenerate
endmodule

// 5-bit equality comparator
module eq5(output eq, input [4:0] a, input [4:0] b);
    wire x0, x1, x2, x3, x4;
    xor2 x_0(.out(x0), .in0(a[0]), .in1(b[0]));
    xor2 x_1(.out(x1), .in0(a[1]), .in1(b[1]));
    xor2 x_2(.out(x2), .in0(a[2]), .in1(b[2]));
    xor2 x_3(.out(x3), .in0(a[3]), .in1(b[3]));
    xor2 x_4(.out(x4), .in0(a[4]), .in1(b[4]));
    wire nx0, nx1, nx2, nx3, nx4;
    not1 n0(.out(nx0), .in0(x0));
    not1 n1(.out(nx1), .in0(x1));
    not1 n2(.out(nx2), .in0(x2));
    not1 n3(.out(nx3), .in0(x3));
    not1 n4(.out(nx4), .in0(x4));
    wire and01;
    and4 a01(.out(and01), .in0(nx0), .in1(nx1), .in2(nx2), .in3(nx3));
    and2 a_last(.out(eq), .in0(and01), .in1(nx4));
endmodule

// IF/ID pipeline register
module if_id_reg(
    input clk,
    input reset,
    input [63:0] pc_in,
    input [63:0] pc_plus4_in,
    input [31:0] instr_in,
    output [63:0] pc_out,
    output [63:0] pc_plus4_out,
    output [31:0] instr_out
    );
    reg64 pc_reg(.q(pc_out), .d(reset ? 64'b0 : pc_in), .clk(clk), .enable(1'b1));
    reg64 pc4_reg(.q(pc_plus4_out), .d(reset ? 64'b0 : pc_plus4_in), .clk(clk), .enable(1'b1));
    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : instr_bits
            reg1 b(.q(instr_out[i]), .d(reset ? 1'b0 : instr_in[i]), .clk(clk), .enable(1'b1));
        end
    endgenerate
endmodule

// ID/EX pipeline register
module id_ex_reg(
    input clk,
    input reset,
    input [63:0] rf_r1_in, rf_r2_in, imm_in, pc_in, pc_plus4_in,
    input [4:0] rd_in, rn_in, rm_in,
    input [4:0] readReg2_in,
    input [18:0] imm19_in,
    input [25:0] imm26_in,
    input [10:0] op_sel_in,
    input [2:0] ALUOp_in,
    input ALUSrc_in, Reg2Loc_in, MemToReg_in, RegWrite_in, MemWrite_in, UncondBr_in, Branch_in,
    output [63:0] rf_r1_out, rf_r2_out, imm_out, pc_out,
    output [63:0] pc_plus4_out,
    output [4:0] rd_out, rn_out, rm_out,
    output [4:0] readReg2_out,
    output [18:0] imm19_out,
    output [25:0] imm26_out,
    output [10:0] op_sel_out,
    output [2:0] ALUOp_out,
    output ALUSrc_out, Reg2Loc_out, MemToReg_out, RegWrite_out, MemWrite_out, UncondBr_out, Branch_out
    );
    // 64-bit fields
    reg64 r_rf_r1(.q(rf_r1_out), .d(reset ? 64'b0 : rf_r1_in), .clk(clk), .enable(1'b1));
    reg64 r_rf_r2(.q(rf_r2_out), .d(reset ? 64'b0 : rf_r2_in), .clk(clk), .enable(1'b1));
    reg64 r_imm(.q(imm_out), .d(reset ? 64'b0 : imm_in), .clk(clk), .enable(1'b1));
    reg64 r_pc(.q(pc_out), .d(reset ? 64'b0 : pc_in), .clk(clk), .enable(1'b1));
    reg64 r_pc4(.q(pc_plus4_out), .d(reset ? 64'b0 : pc_plus4_in), .clk(clk), .enable(1'b1));

    // small fields
    regN #(.N(5)) r_rd(.q(rd_out), .d(reset ? 5'b0 : rd_in), .clk(clk), .enable(1'b1));
    regN #(.N(5)) r_rn(.q(rn_out), .d(reset ? 5'b0 : rn_in), .clk(clk), .enable(1'b1));
    regN #(.N(5)) r_rm(.q(rm_out), .d(reset ? 5'b0 : rm_in), .clk(clk), .enable(1'b1));
    regN #(.N(5)) r_r2(.q(readReg2_out), .d(reset ? 5'b0 : readReg2_in), .clk(clk), .enable(1'b1));
    regN #(.N(11)) r_op(.q(op_sel_out), .d(reset ? 11'b0 : op_sel_in), .clk(clk), .enable(1'b1));
    regN #(.N(3)) r_aluctrl(.q(ALUOp_out), .d(reset ? 3'b0 : ALUOp_in), .clk(clk), .enable(1'b1));
    // immediates
    regN #(.N(19)) r_i19(.q(imm19_out), .d(reset ? 19'b0 : imm19_in), .clk(clk), .enable(1'b1));
    regN #(.N(26)) r_i26(.q(imm26_out), .d(reset ? 26'b0 : imm26_in), .clk(clk), .enable(1'b1));

    // single-bit control signals
    reg1 r_a(.q(ALUSrc_out), .d(reset ? 1'b0 : ALUSrc_in), .clk(clk), .enable(1'b1));
    reg1 r_r2l(.q(Reg2Loc_out), .d(reset ? 1'b0 : Reg2Loc_in), .clk(clk), .enable(1'b1));
    reg1 r_mtr(.q(MemToReg_out), .d(reset ? 1'b0 : MemToReg_in), .clk(clk), .enable(1'b1));
    reg1 r_rw(.q(RegWrite_out), .d(reset ? 1'b0 : RegWrite_in), .clk(clk), .enable(1'b1));
    reg1 r_mw(.q(MemWrite_out), .d(reset ? 1'b0 : MemWrite_in), .clk(clk), .enable(1'b1));
    reg1 r_ub(.q(UncondBr_out), .d(reset ? 1'b0 : UncondBr_in), .clk(clk), .enable(1'b1));
    reg1 r_b(.q(Branch_out), .d(reset ? 1'b0 : Branch_in), .clk(clk), .enable(1'b1));
endmodule

// EX/MEM pipeline register
module ex_mem_reg(
    input clk,
    input reset,
    input [63:0] alu_out_in, write_data_in, pc_in,
    input [63:0] pc_plus4_in,
    input [4:0] rd_in,
    input [18:0] imm19_in,
    input [25:0] imm26_in,
    input MemToReg_in, RegWrite_in, MemWrite_in,
    input [10:0] op_sel_in,
    // ALU flags forwarded
    input alu_neg_in, alu_zero_in, alu_ovf_in, alu_carry_in,
    output [63:0] alu_out_out, write_data_out, pc_out, pc_plus4_out,
    output [4:0] rd_out,
    output [18:0] imm19_out,
    output [25:0] imm26_out,
    output MemToReg_out, RegWrite_out, MemWrite_out,
    output [10:0] op_sel_out,
    output alu_neg_out, alu_zero_out, alu_ovf_out, alu_carry_out
    );
    reg64 r_alu(.q(alu_out_out), .d(reset ? 64'b0 : alu_out_in), .clk(clk), .enable(1'b1));
    reg64 r_wd(.q(write_data_out), .d(reset ? 64'b0 : write_data_in), .clk(clk), .enable(1'b1));
    reg64 r_pc(.q(pc_out), .d(reset ? 64'b0 : pc_in), .clk(clk), .enable(1'b1));
    reg64 r_pc4(.q(pc_plus4_out), .d(reset ? 64'b0 : pc_plus4_in), .clk(clk), .enable(1'b1));
    regN #(.N(5)) r_rd(.q(rd_out), .d(reset ? 5'b0 : rd_in), .clk(clk), .enable(1'b1));
    regN #(.N(19)) r_i19(.q(imm19_out), .d(reset ? 19'b0 : imm19_in), .clk(clk), .enable(1'b1));
    regN #(.N(26)) r_i26(.q(imm26_out), .d(reset ? 26'b0 : imm26_in), .clk(clk), .enable(1'b1));
    reg1 r_mtr(.q(MemToReg_out), .d(reset ? 1'b0 : MemToReg_in), .clk(clk), .enable(1'b1));
    reg1 r_rw(.q(RegWrite_out), .d(reset ? 1'b0 : RegWrite_in), .clk(clk), .enable(1'b1));
    reg1 r_mw(.q(MemWrite_out), .d(reset ? 1'b0 : MemWrite_in), .clk(clk), .enable(1'b1));
    regN #(.N(11)) r_op(.q(op_sel_out), .d(reset ? 11'b0 : op_sel_in), .clk(clk), .enable(1'b1));
    reg1 r_neg(.q(alu_neg_out), .d(reset ? 1'b0 : alu_neg_in), .clk(clk), .enable(1'b1));
    reg1 r_zero(.q(alu_zero_out), .d(reset ? 1'b0 : alu_zero_in), .clk(clk), .enable(1'b1));
    reg1 r_ovf(.q(alu_ovf_out), .d(reset ? 1'b0 : alu_ovf_in), .clk(clk), .enable(1'b1));
    reg1 r_carry(.q(alu_carry_out), .d(reset ? 1'b0 : alu_carry_in), .clk(clk), .enable(1'b1));
endmodule

// MEM/WB pipeline register
module mem_wb_reg(
    input clk,
    input reset,
    input [63:0] mem_out_in, alu_out_in, write_data_in, pc_in, pc_plus4_in,
    input [4:0] rd_in, 
    input [18:0] imm19_in,
    input [25:0] imm26_in,
    input MemToReg_in, RegWrite_in,
    input [10:0] op_sel_in,
    // ALU flags from EX/MEM
    input alu_neg_in, alu_zero_in, alu_ovf_in, alu_carry_in,
    output [63:0] mem_out_out, alu_out_out, write_data_out, pc_out, pc_plus4_out,
    output [4:0] rd_out,
    output [18:0] imm19_out,
    output [25:0] imm26_out,
    output MemToReg_out, RegWrite_out,
    output [10:0] op_sel_out,
    output alu_neg_out, alu_zero_out, alu_ovf_out, alu_carry_out
    );
    reg64 r_mem(.q(mem_out_out), .d(reset ? 64'b0 : mem_out_in), .clk(clk), .enable(1'b1));
    reg64 r_alu(.q(alu_out_out), .d(reset ? 64'b0 : alu_out_in), .clk(clk), .enable(1'b1));
    reg64 r_wd(.q(write_data_out), .d(reset ? 64'b0 : write_data_in), .clk(clk), .enable(1'b1));
    reg64 r_pc(.q(pc_out), .d(reset ? 64'b0 : pc_in), .clk(clk), .enable(1'b1));
    reg64 r_pc4(.q(pc_plus4_out), .d(reset ? 64'b0 : pc_plus4_in), .clk(clk), .enable(1'b1));
    regN #(.N(5)) r_rd(.q(rd_out), .d(reset ? 5'b0 : rd_in), .clk(clk), .enable(1'b1));
    regN #(.N(19)) r_i19(.q(imm19_out), .d(reset ? 19'b0 : imm19_in), .clk(clk), .enable(1'b1));
    regN #(.N(26)) r_i26(.q(imm26_out), .d(reset ? 26'b0 : imm26_in), .clk(clk), .enable(1'b1));
    reg1 r_mtr(.q(MemToReg_out), .d(reset ? 1'b0 : MemToReg_in), .clk(clk), .enable(1'b1));
    reg1 r_rw(.q(RegWrite_out), .d(reset ? 1'b0 : RegWrite_in), .clk(clk), .enable(1'b1));
    regN #(.N(11)) r_op(.q(op_sel_out), .d(reset ? 11'b0 : op_sel_in), .clk(clk), .enable(1'b1));
    reg1 r_neg(.q(alu_neg_out), .d(reset ? 1'b0 : alu_neg_in), .clk(clk), .enable(1'b1));
    reg1 r_zero(.q(alu_zero_out), .d(reset ? 1'b0 : alu_zero_in), .clk(clk), .enable(1'b1));
    reg1 r_ovf(.q(alu_ovf_out), .d(reset ? 1'b0 : alu_ovf_in), .clk(clk), .enable(1'b1));
    reg1 r_carry(.q(alu_carry_out), .d(reset ? 1'b0 : alu_carry_in), .clk(clk), .enable(1'b1));
endmodule

// Combinational hazard and forwarding unit
module hazard_unit(
    input  [10:0] hz_op_sel_ex,
    input  [10:0] hz_op_sel_exmem,
    input  [10:0] hz_op_sel_memwb,
    input  [4:0] hz_rd_ex, hz_rd_exmem, hz_rd_memwb,
    input  hz_exmem_RegWrite, hz_memwb_RegWrite,
    // RegWrite_ex can decide EX->ID forwarding
    input  hz_RegWrite_ex,
    input  hz_MemToReg_ex, hz_exmem_MemToReg, hz_MemToReg_wb,
    input  hz_alu_neg_pre, hz_exmem_alu_neg, hz_alu_neg_wb,
    // architected flags from WB (lowest priority fallback)
    input  hz_alu_neg_arch,
    input  hz_alu_ovf_pre, hz_exmem_alu_ovf, hz_alu_ovf_wb,
    input  hz_alu_ovf_arch,
    input  hz_alu_zero_pre, hz_exmem_alu_zero, hz_alu_zero_wb,
    input  hz_alu_zero_arch,
    input  [4:0] hz_readReg2_id,
    // inputs providing data sources for forwarding decision
    input  [63:0] hz_rf_r2_id,
    input  [63:0] hz_alu_pre,
    input  [63:0] hz_exmem_alu,
    input  [63:0] hz_memwb_alu,
    input  [63:0] hz_memwb_mem,
    output hz_forwarded_neg_to_id, hz_forwarded_ovf_to_id, hz_forwarded_zero_to_id,
    // Data-forwarding outputs for ID's zero detection (CBZ)
    output [63:0] hz_forwarded_r2_val,
    output hz_forwarded_r2_sel
    );

    // detect SUBS opcode in stage fields
    wire sel_ex_subs = hz_op_sel_ex[10];
    wire sel_exmem_subs = hz_op_sel_exmem[10];
    wire sel_memwb_subs = hz_op_sel_memwb[10];

    // Forward NEG flag with priority: EX -> EX/MEM -> MEM/WB -> ARCH
    // Level 0: choose between MEM/WB and ARCH
    wire sel_memwb_n; not1 n_sel_memwb(.out(sel_memwb_n), .in0(sel_memwb_subs));
    wire memwb_and_neg; and2 a_memwbn(.out(memwb_and_neg), .in0(sel_memwb_subs), .in1(hz_alu_neg_wb));
    wire memwb_and_arch_neg; and2 a_memwba(.out(memwb_and_arch_neg), .in0(sel_memwb_n), .in1(hz_alu_neg_arch));
    wire memwb_choice_neg; or2 o_memwb_choice_neg(.out(memwb_choice_neg), .in0(memwb_and_neg), .in1(memwb_and_arch_neg));
    // Level 1: exmem vs (memwb_choice)
    wire sel_exmem_n; not1 n_sel_exmem(.out(sel_exmem_n), .in0(sel_exmem_subs));
    wire exmem_and_neg; and2 a_exmemn(.out(exmem_and_neg), .in0(sel_exmem_subs), .in1(hz_exmem_alu_neg));
    wire exmem_and_fallback_neg; and2 a_exmemf(.out(exmem_and_fallback_neg), .in0(sel_exmem_n), .in1(memwb_choice_neg));
    wire exmem_choice_neg; or2 o_exmem_choice_neg(.out(exmem_choice_neg), .in0(exmem_and_neg), .in1(exmem_and_fallback_neg));
    // Level 2: ex vs (exmem_choice)
    wire sel_ex_n; not1 n_sel_ex(.out(sel_ex_n), .in0(sel_ex_subs));
    wire ex_and_neg; and2 a_exn(.out(ex_and_neg), .in0(sel_ex_subs), .in1(hz_alu_neg_pre));
    wire ex_and_fallback_neg; and2 a_exf(.out(ex_and_fallback_neg), .in0(sel_ex_n), .in1(exmem_choice_neg));
    or2 o_final_neg(.out(hz_forwarded_neg_to_id), .in0(ex_and_neg), .in1(ex_and_fallback_neg));

    // OVF forwarding (same priority chain)
    wire memwb_and_ovf; and2 a_memwbev(.out(memwb_and_ovf), .in0(sel_memwb_subs), .in1(hz_alu_ovf_wb));
    wire memwb_and_arch_ovf; and2 a_memwbaov(.out(memwb_and_arch_ovf), .in0(sel_memwb_n), .in1(hz_alu_ovf_arch));
    wire memwb_choice_ovf; or2 o_memwb_choice_ovf(.out(memwb_choice_ovf), .in0(memwb_and_ovf), .in1(memwb_and_arch_ovf));

    wire exmem_and_ovf; and2 a_exmemov(.out(exmem_and_ovf), .in0(sel_exmem_subs), .in1(hz_exmem_alu_ovf));
    wire exmem_and_fallback_ovf; and2 a_exmemfov(.out(exmem_and_fallback_ovf), .in0(sel_exmem_n), .in1(memwb_choice_ovf));
    wire exmem_choice_ovf; or2 o_exmem_choice_ovf(.out(exmem_choice_ovf), .in0(exmem_and_ovf), .in1(exmem_and_fallback_ovf));

    wire ex_and_ovf; and2 a_exov(.out(ex_and_ovf), .in0(sel_ex_subs), .in1(hz_alu_ovf_pre));
    wire ex_and_fallback_ovf; and2 a_exfov(.out(ex_and_fallback_ovf), .in0(sel_ex_n), .in1(exmem_choice_ovf));
    or2 o_final_ovf(.out(hz_forwarded_ovf_to_id), .in0(ex_and_ovf), .in1(ex_and_fallback_ovf));

    // ZERO forwarding (same priority chain)
    wire memwb_and_zero; and2 a_memwbz(.out(memwb_and_zero), .in0(sel_memwb_subs), .in1(hz_alu_zero_wb));
    wire memwb_and_arch_zero; and2 a_memwba_z(.out(memwb_and_arch_zero), .in0(sel_memwb_n), .in1(hz_alu_zero_arch));
    wire memwb_choice_zero; or2 o_memwb_choice_zero(.out(memwb_choice_zero), .in0(memwb_and_zero), .in1(memwb_and_arch_zero));

    wire exmem_and_zero; and2 a_exmemz(.out(exmem_and_zero), .in0(sel_exmem_subs), .in1(hz_exmem_alu_zero));
    wire exmem_and_fallback_zero; and2 a_exmemfz(.out(exmem_and_fallback_zero), .in0(sel_exmem_n), .in1(memwb_choice_zero));
    wire exmem_choice_zero; or2 o_exmem_choice_zero(.out(exmem_choice_zero), .in0(exmem_and_zero), .in1(exmem_and_fallback_zero));

    wire ex_and_zero; and2 a_exz(.out(ex_and_zero), .in0(sel_ex_subs), .in1(hz_alu_zero_pre));
    wire ex_and_fallback_zero; and2 a_exfz(.out(ex_and_fallback_zero), .in0(sel_ex_n), .in1(exmem_choice_zero));
    or2 o_final_zero(.out(hz_forwarded_zero_to_id), .in0(ex_and_zero), .in1(ex_and_fallback_zero));

    // Forward register-2 for CBZ (priority EX -> EX/MEM -> MEM/WB)
    // Centralized forwarding logic for forwarded_r2
    wire ex_eq_r2; eq5 eq_exr2(.eq(ex_eq_r2), .a(hz_rd_ex), .b(hz_readReg2_id));
    wire exmem_eq_r2; eq5 eq_exmemr2(.eq(exmem_eq_r2), .a(hz_rd_exmem), .b(hz_readReg2_id));
    wire memwb_eq_r2; eq5 eq_memwbr2(.eq(memwb_eq_r2), .a(hz_rd_memwb), .b(hz_readReg2_id));

    // suppress forwarding when destination is X31 (zero register)
    wire rd_ex_is31; eq5 eq_rdex31(.eq(rd_ex_is31), .a(hz_rd_ex), .b(5'b11111));
    wire rd_ex_not31; not1 n_rdex31(.out(rd_ex_not31), .in0(rd_ex_is31));
    wire rd_exmem_is31; eq5 eq_rdexmem31(.eq(rd_exmem_is31), .a(hz_rd_exmem), .b(5'b11111));
    wire rd_exmem_not31; not1 n_rdexmem31(.out(rd_exmem_not31), .in0(rd_exmem_is31));
    wire rd_memwb_is31; eq5 eq_rdmemwb31(.eq(rd_memwb_is31), .a(hz_rd_memwb), .b(5'b11111));
    wire rd_memwb_not31; not1 n_rdmemwb31(.out(rd_memwb_not31), .in0(rd_memwb_is31));

    // EX forward: writing, matching, not X31, and not a load
    wire sel_ex_fwd_tmp; and3 a_sexf(.out(sel_ex_fwd_tmp), .in0(hz_RegWrite_ex), .in1(ex_eq_r2), .in2(rd_ex_not31));
    wire ex_not_load; not1 n_ex_not_load(.out(ex_not_load), .in0(hz_MemToReg_ex));
    wire sel_ex_fwd; and2 a_sexf_ok(.out(sel_ex_fwd), .in0(sel_ex_fwd_tmp), .in1(ex_not_load));

    // EX/MEM forward: writing, matching, not X31, and not a load
    wire sel_exmem_fwd_tmp; and3 a_sememf(.out(sel_exmem_fwd_tmp), .in0(hz_exmem_RegWrite), .in1(exmem_eq_r2), .in2(rd_exmem_not31));
    wire exmem_not_load; not1 n_exmem_not_load(.out(exmem_not_load), .in0(hz_exmem_MemToReg));
    wire sel_exmem_fwd; and2 a_sememf_ok(.out(sel_exmem_fwd), .in0(sel_exmem_fwd_tmp), .in1(exmem_not_load));

    // MEM/WB forward: writeback stage (forward mem or alu result)
    wire sel_memwb_fwd; and3 a_smemwbf(.out(sel_memwb_fwd), .in0(hz_memwb_RegWrite), .in1(memwb_eq_r2), .in2(rd_memwb_not31));

    // memwb forward value selected by MemToReg
    wire memwb_sel_n; not1 n_memwb_sel(.out(memwb_sel_n), .in0(hz_MemToReg_wb));
    wire [63:0] memwb_forward_val; mux2_1_64 memwb_mux(.in0(hz_memwb_alu), .in1(hz_memwb_mem), .sel(hz_MemToReg_wb), .sel_n(memwb_sel_n), .out(memwb_forward_val));

    // Chain forwards: EX -> EX/MEM -> MEM/WB -> RF
    wire [63:0] tmp_r2_memwb;
    wire sel_memwb_fwd_n; not1 n_smemwb(.out(sel_memwb_fwd_n), .in0(sel_memwb_fwd));
    mux2_1_64 mux_r2_memwb_first(.in0(hz_rf_r2_id), .in1(memwb_forward_val), .sel(sel_memwb_fwd), .sel_n(sel_memwb_fwd_n), .out(tmp_r2_memwb));

    wire [63:0] tmp_r2_exmem;
    wire sel_exmem_fwd_n; not1 n_sememn(.out(sel_exmem_fwd_n), .in0(sel_exmem_fwd));
    mux2_1_64 mux_r2_exmem(.in0(tmp_r2_memwb), .in1(hz_exmem_alu), .sel(sel_exmem_fwd), .sel_n(sel_exmem_fwd_n), .out(tmp_r2_exmem));

    wire [63:0] tmp_r2_ex;
    wire sel_ex_fwd_n; not1 n_sexfn(.out(sel_ex_fwd_n), .in0(sel_ex_fwd));
    mux2_1_64 mux_r2_ex(.in0(tmp_r2_exmem), .in1(hz_alu_pre), .sel(sel_ex_fwd), .sel_n(sel_ex_fwd_n), .out(tmp_r2_ex));

    assign hz_forwarded_r2_val = tmp_r2_ex;

    // final select signal: any of the three forwarding sources 
    wire any_fwd_ex_or_exmem; or2 o_any1(.out(any_fwd_ex_or_exmem), .in0(sel_ex_fwd), .in1(sel_exmem_fwd));
    or2 o_any2(.out(hz_forwarded_r2_sel), .in0(any_fwd_ex_or_exmem), .in1(sel_memwb_fwd));
endmodule

module id_stage(
    input  clk,
    input  [31:0] instr,
    input  [63:0] pc_in,
    // writeback inputs from WB stage
    input  [63:0] wb_WriteData,
    input  [4:0]  wb_WriteRegister,
    input         wb_RegWrite,
    // forwarded flags (combined / prioritized) for B.cond evaluation
    input         flag_neg_in,
    input         flag_ovf_in,
    input         flag_zero_in,
    // optional forwarded register-2 value and select for CBZ (priority forwarded value -> rf_r2)
    input  [63:0] forwarded_r2,
    input         forwarded_r2_sel,

    // read outputs
    output [63:0] rf_r1,
    output [63:0] rf_r2,
    output [4:0] rd, rn, rm,
    output [4:0] readReg2,
    output [11:0] imm12,
    output [18:0] imm19,
    output [25:0] imm26,
    output [8:0]  imm9,
    output [5:0]  shamt,
    output [63:0] imm_selected,
    output [10:0] op_sel,
    // branch outputs: decision and target computed in ID
    output        branch_taken_out,
    output [63:0] branch_target_out,
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

    // instruction fields
    assign rd    = instr[4:0];
    assign rn    = instr[9:5];
    assign rm    = instr[20:16];
    assign imm12 = instr[21:10];
    assign imm19 = instr[23:5];
    assign imm26 = instr[25:0];
    assign imm9  = instr[20:12];
    assign shamt = instr[15:10];

    // control unit (decode)
    wire cu_Reg2Loc, cu_ALUSrc, cu_MemToReg, cu_RegWrite, cu_MemWrite, cu_UncondBr, cu_Branch;
    wire [2:0] cu_ALUOp;
    control_unit cu(.op_sel(op_sel), .Reg2Loc(cu_Reg2Loc), .ALUSrc(cu_ALUSrc), .MemToReg(cu_MemToReg), .RegWrite(cu_RegWrite), .MemWrite(cu_MemWrite), .UncondBr(cu_UncondBr), .Branch(cu_Branch), .ALUOp(cu_ALUOp));

    // Select readReg2: Rt (instr[4:0]) or Rm (instr[20:16]) via Reg2Loc
    wire cu_Reg2Loc_n;
    not1 n_reg2loc(.out(cu_Reg2Loc_n), .in0(cu_Reg2Loc));
    mux2_1_5 reg2_mux(.in0(instr[4:0]), .in1(instr[20:16]), .sel(cu_Reg2Loc), .sel_n(cu_Reg2Loc_n), .out(readReg2));

    // Invert clk for regfile so WB writes are visible in same cycle
    wire nclk;
    not1 nclk_inv(.out(nclk), .in0(clk));

    // register file instance - write ports come from WB stage
    regfile rf(.ReadData1(rf_r1), .ReadData2(rf_r2), .WriteData(wb_WriteData),
        .ReadRegister1(rn), .ReadRegister2(readReg2), .WriteRegister(wb_WriteRegister),
        .RegWrite(wb_RegWrite), .clk(nclk));

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
    wire [9:0] op10 = instr[31:22];
    wire [10:0] op11 = instr[31:21];
    wire [7:0] op8 = instr[31:24];
    wire [5:0] op6 = instr[31:26];
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

    // immediates formatting
    wire [63:0] imm64_addi = {{52'b0}, imm12};
    wire [63:0] imm64_ldst = {{55{imm9[8]}}, imm9};
    wire [63:0] imm64_shamt = {58'b0, shamt};
    wire sel_ldst;
    or2 or_ldst(.out(sel_ldst), .in0(is_ldur), .in1(is_stur));
    wire [1:0] imm_sel = {is_lsr, sel_ldst};
    wire [1:0] imm_sel_n;
    not1 n_sel0(.out(imm_sel_n[0]), .in0(imm_sel[0]));
    not1 n_sel1(.out(imm_sel_n[1]), .in0(imm_sel[1]));
    mux4_1_64 imm_mux(.input_({imm64_addi, imm64_ldst, imm64_shamt, 64'b0}), .sel(imm_sel), .sel_n(imm_sel_n), .out(imm_selected));

    // Branch target computation (sign-extend and shift-left-2)
    wire [63:0] b_offset_id   = {{36{imm26[25]}}, imm26, 2'b00};
    wire [63:0] cbz_offset_id = {{43{imm19[18]}}, imm19, 2'b00};
    wire [63:0] blt_offset_id = {{43{imm19[18]}}, imm19, 2'b00};
    wire [63:0] b_target_id; wire [63:0] cbz_target_id; wire [63:0] blt_target_id;
    adder64 id_btarget(.in0(pc_in), .in1(b_offset_id), .cin(1'b0), .sum(b_target_id), .cout());
    adder64 id_cbztarget(.in0(pc_in), .in1(cbz_offset_id), .cin(1'b0), .sum(cbz_target_id), .cout());
    adder64 id_blttarget(.in0(pc_in), .in1(blt_offset_id), .cin(1'b0), .sum(blt_target_id), .cout());

    // Allow forwarded value to override rf_r2 for CBZ zero detection
    wire forwarded_r2_sel_n; not1 n_fwd_r2(.out(forwarded_r2_sel_n), .in0(forwarded_r2_sel));
    wire [63:0] zero_src;
    mux2_1_64 mux_zero_src(.in0(rf_r2), .in1(forwarded_r2), .sel(forwarded_r2_sel), .sel_n(forwarded_r2_sel_n), .out(zero_src));
    wire is_zero; zero_detect zd(.data(zero_src), .zero(is_zero));

    // BLT condition: NEG != OVF
    wire blt_cond_id; xor2 x_blt_id(.out(blt_cond_id), .in0(flag_neg_in), .in1(flag_ovf_in));

    // Branch decision and target (priority: B > BLT > CBZ)
    wire branch_taken_w;
    assign branch_taken_w = is_b | (is_blt & blt_cond_id) | (is_cbz & is_zero);

    // Select branch target with priority: CBZ -> BLT -> B
    wire [63:0] tmp0; wire sel_cbz_n_id; not1 n_cbzn_id(.out(sel_cbz_n_id), .in0(is_cbz));
    mux2_1_64 mux0(.in0(64'b0), .in1(cbz_target_id), .sel(is_cbz), .sel_n(sel_cbz_n_id), .out(tmp0));
    wire [63:0] tmp1; wire sel_blt_n_id; not1 n_blt_id(.out(sel_blt_n_id), .in0(is_blt));
    mux2_1_64 mux1(.in0(tmp0), .in1(blt_target_id), .sel(is_blt), .sel_n(sel_blt_n_id), .out(tmp1));
    wire [63:0] tmp2; wire sel_b_n_id; not1 n_bn_id(.out(sel_b_n_id), .in0(is_b));
    mux2_1_64 mux2(.in0(tmp1), .in1(b_target_id), .sel(is_b), .sel_n(sel_b_n_id), .out(tmp2));

    assign branch_taken_out = branch_taken_w;
    assign branch_target_out = tmp2;
endmodule

// EXE stage: performs forwarding, ALU operation and writes EX/MEM register
module exe_stage(
    input clk,
    // inputs from ID/EX used by EX combinational logic
    input [63:0] rf_r1_ex, rf_r2_ex, imm_ex,
    input [4:0] rn_ex, readReg2_ex,
    input [2:0] ALUOp_ex,
    input ALUSrc_ex,
    input [10:0] op_sel,
    // inputs from previous pipeline registers for forwarding
    input [4:0] rd_exmem_in, rd_memwb_in,
    input exmem_RegWrite_in, memwb_RegWrite_in,
    input exmem_MemToReg_in, memwb_MemToReg_in,
    input [63:0] exmem_alu_in, memwb_alu_in, memwb_mem_in,
    // outputs: ALU result and store data (unregistered)
    output [63:0] alu_out_pre, write_data_pre,
    // ALU flags (pre-register)
    output alu_neg_pre, alu_zero_pre, alu_ovf_pre, alu_carry_pre
    );

    // comparator instances for source registers
    wire exmem_eq_rd_rn; eq5 eq_a(.eq(exmem_eq_rd_rn), .a(rd_exmem_in), .b(rn_ex));
    wire exmem_eq_rd_r2; eq5 eq_b(.eq(exmem_eq_rd_r2), .a(rd_exmem_in), .b(readReg2_ex));
    wire memwb_eq_rd_rn; eq5 eq_c(.eq(memwb_eq_rd_rn), .a(rd_memwb_in), .b(rn_ex));
    wire memwb_eq_rd_r2; eq5 eq_d(.eq(memwb_eq_rd_r2), .a(rd_memwb_in), .b(readReg2_ex));

    // forward control signals
    wire selA_exmem; and2 a_selA(.out(selA_exmem), .in0(exmem_RegWrite_in), .in1(exmem_eq_rd_rn));
    wire selB_exmem; and2 a_selB(.out(selB_exmem), .in0(exmem_RegWrite_in), .in1(exmem_eq_rd_r2));
    // block EX/MEM forward if it's a load (EX/MEM.MemToReg==1)
    wire exmem_not_load; not1 nl(.out(exmem_not_load), .in0(exmem_MemToReg_in));
    // prevent forwarding when destination register is X31
    wire rd_exmem_is31; eq5 eq_rdex31(.eq(rd_exmem_is31), .a(rd_exmem_in), .b(5'b11111));
    wire rd_exmem_not31; not1 n_rdex31(.out(rd_exmem_not31), .in0(rd_exmem_is31));
    wire selA_exmem_final; and3 a_selA_f(.out(selA_exmem_final), .in0(selA_exmem), .in1(exmem_not_load), .in2(rd_exmem_not31));
    wire selB_exmem_final; and3 a_selB_f(.out(selB_exmem_final), .in0(selB_exmem), .in1(exmem_not_load), .in2(rd_exmem_not31));

    // also prevent MEM/WB forwarding when destination is X31
    wire rd_memwb_is31; eq5 eq_rdmemwb31(.eq(rd_memwb_is31), .a(rd_memwb_in), .b(5'b11111));
    wire rd_memwb_not31; not1 n_rdmemwb(.out(rd_memwb_not31), .in0(rd_memwb_is31));
    wire selA_memwb; and3 a_selA2(.out(selA_memwb), .in0(memwb_RegWrite_in), .in1(memwb_eq_rd_rn), .in2(rd_memwb_not31));
    wire selB_memwb; and3 a_selB2(.out(selB_memwb), .in0(memwb_RegWrite_in), .in1(memwb_eq_rd_r2), .in2(rd_memwb_not31));

    // prepare memwb forward source value (choose mem or alu depending on MemToReg)
    wire memwb_sel_n; not1 n_memwb(.out(memwb_sel_n), .in0(memwb_MemToReg_in));
    wire [63:0] memwb_forward_val;
    mux2_1_64 memwb_val_mux(.in0(memwb_alu_in), .in1(memwb_mem_in), .sel(memwb_MemToReg_in), .sel_n(memwb_sel_n), .out(memwb_forward_val));

    // ALU A input forwarding: priority EX/MEM > MEM/WB > RF
    wire [63:0] a_tmp0;
    wire selA_memwb_n; not1 nAmem(.out(selA_memwb_n), .in0(selA_memwb));
    mux2_1_64 muxA_memwb_first(.in0(rf_r1_ex), .in1(memwb_forward_val), .sel(selA_memwb), .sel_n(selA_memwb_n), .out(a_tmp0));

    wire [63:0] a_final;
    wire selA_exmem_n; not1 nAex(.out(selAex_n), .in0(selA_exmem_final));
    // select exmem over the tmp0
    mux2_1_64 muxA_exmem_then(.in0(a_tmp0), .in1(exmem_alu_in), .sel(selA_exmem_final), .sel_n(selAex_n), .out(a_final));

    // ALU B input forwarding (before ALUSrc): EX/MEM > MEM/WB > RF
    wire [63:0] b_tmp0;
    wire selB_memwb_n; not1 nBmem(.out(selB_memwb_n), .in0(selB_memwb));
    mux2_1_64 muxB_memwb_first(.in0(rf_r2_ex), .in1(memwb_forward_val), .sel(selB_memwb), .sel_n(selB_memwb_n), .out(b_tmp0));

    wire [63:0] b_after_memwb;
    wire selB_exmem_n; not1 nBex(.out(selBex_n), .in0(selB_exmem_final));
    mux2_1_64 muxB_exmem_then(.in0(b_tmp0), .in1(exmem_alu_in), .sel(selB_exmem_final), .sel_n(selBex_n), .out(b_after_memwb));

    // final B selection with immediate
    wire [63:0] b_final;
    wire ALUSrc_ex_n; not1 nALUSrc(.out(ALUSrc_ex_n), .in0(ALUSrc_ex));
    mux2_1_64 muxB_final(.in0(b_after_memwb), .in1(imm_ex), .sel(ALUSrc_ex), .sel_n(ALUSrc_ex_n), .out(b_final));

    // ALU instance
    wire [63:0] alu_out_ex;
    wire alu_neg_ex, alu_zero_ex, alu_ovf_ex, alu_carry_ex;
    alu alu_inst(.A(a_final), .B(b_final), .cntrl(ALUOp_ex), .result(alu_out_ex), .negative(alu_neg_ex), .zero(alu_zero_ex), .overflow(alu_ovf_ex), .carry_out(alu_carry_ex));

    // EX outputs (pre-register) - ALU result and forwarded store data
    assign alu_out_pre = alu_out_ex;
    assign write_data_pre = b_after_memwb;
    assign alu_neg_pre = alu_neg_ex;
    assign alu_zero_pre = alu_zero_ex;
    assign alu_ovf_pre = alu_ovf_ex;
    assign alu_carry_pre = alu_carry_ex;
endmodule

// Top-level pipelined CPU
module cpu_pipelined(
    input clk,
    input rst
    );
    // IF stage wires
    wire [63:0] pc_in, pc_out, pc_plus4_if;
    wire [31:0] instr_if;
    wire [31:0] instr_id;

    instr_stage ifs(.clk(clk), .pc_in(pc_in), .pc_out(pc_out), .instr(instr_if), .pc_plus4(pc_plus4_if));

    // --- IF/ID register wiring ---
    wire [63:0] pc_id_pc, pc_plus4_id;
    if_id_reg ifid(.clk(clk), .reset(rst), .pc_in(pc_out), .pc_plus4_in(pc_plus4_if), .instr_in(instr_if), .pc_out(pc_id_pc), .pc_plus4_out(pc_plus4_id), .instr_out(instr_id));

    // ID stage wires
    wire [4:0] rd_id, rn_id, rm_id, readReg2_id;
    wire [11:0] imm12_id; wire [18:0] imm19_id; wire [25:0] imm26_id; wire [8:0] imm9_id; wire [5:0] shamt_id;
    // outputs from id_stage
    wire [63:0] imm_selected_id;
    wire [10:0] op_sel_id;
    wire [2:0]  cu_ALUOp;
    // control outputs from id_stage
    wire cu_Reg2Loc, cu_ALUSrc, cu_MemToReg, cu_RegWrite, cu_MemWrite, cu_UncondBr, cu_Branch;
    
    wire [63:0] rf_ReadData1, rf_ReadData2;
    // Writeback signals (driven by MEM/WB stage and used by ID stage)
    wire [63:0] wb_write_data;
    wire [4:0] rd_wb;
    wire RegWrite_wb;

    // hazard forwarding logic
    wire forwarded_neg_to_id, forwarded_ovf_to_id, forwarded_zero_to_id;
    // --- Forward register value for ID (for CBZ) ---
    // priority: EX (alu_pre) -> EX/MEM (exmem_alu_out) -> MEM/WB (memwb_mem_out/memwb_alu_out)
    wire [63:0] forwarded_r2_val;
    wire forwarded_r2_sel;

    // --- ID/EX register: capture decoded values and control signals ---
    wire [63:0] rf_r1_ex, rf_r2_ex, imm_ex, pc_ex, pc4_ex;
    wire [4:0] rd_ex, rn_ex, rm_ex, readReg2_ex;
    wire [18:0] imm19_ex; wire [25:0] imm26_ex;
    wire [10:0] op_sel_ex; wire [2:0] ALUOp_ex;
    wire ALUSrc_ex, Reg2Loc_ex, MemToReg_ex, RegWrite_ex, MemWrite_ex, UncondBr_ex, Branch_ex;

    // Use exe_stage to handle forwarding, ALU and EX/MEM register
    wire [63:0] exmem_alu_out, exmem_write_data_out, exmem_pc_out, exmem_pc4_out;
    wire [4:0] rd_exmem; wire [18:0] exmem_imm19_out; wire [25:0] exmem_imm26_out;
    wire exmem_MemToReg, exmem_RegWrite, exmem_MemWrite;
    wire [10:0] exmem_op_out;
    wire exmem_alu_neg_out, exmem_alu_zero_out, exmem_alu_ovf_out, exmem_alu_carry_out;

    // wires for EX pre-register outputs (to be captured by top-level ex_mem_reg)
    wire [63:0] alu_pre, write_data_pre;
    wire alu_neg_pre, alu_zero_pre, alu_ovf_pre, alu_carry_pre;

    // MEM/WB outputs (declare before exe_stage usage so exe_stage can reference them)
    wire [63:0] memwb_mem_out, memwb_alu_out, memwb_write_data, memwb_pc, memwb_pc4;
    wire [4:0] rd_memwb; wire [18:0] memwb_imm19; wire [25:0] memwb_imm26;
    wire [10:0] op_sel_wb; 
    wire MemToReg_wb;
    wire memwb_RegWrite;
    wire alu_neg_wb, alu_zero_wb, alu_ovf_wb, alu_carry_wb;
    
    wire flag_neg_q_w, flag_zero_q_w, flag_ovf_q_w, flag_carry_q_w;

    hazard_unit hz(
        .hz_op_sel_ex(op_sel_ex), .hz_op_sel_exmem(exmem_op_out), .hz_op_sel_memwb(op_sel_wb), .hz_rd_ex(rd_ex), .hz_rd_exmem(rd_exmem), 
        .hz_rd_memwb(rd_memwb), .hz_exmem_RegWrite(exmem_RegWrite), .hz_memwb_RegWrite(memwb_RegWrite), .hz_RegWrite_ex(RegWrite_ex),
        .hz_MemToReg_ex(MemToReg_ex), .hz_exmem_MemToReg(exmem_MemToReg), .hz_MemToReg_wb(MemToReg_wb), .hz_alu_neg_pre(alu_neg_pre), 
        .hz_exmem_alu_neg(exmem_alu_neg_out), .hz_alu_neg_wb(alu_neg_wb), .hz_alu_neg_arch(flag_neg_q_w), .hz_alu_ovf_pre(alu_ovf_pre), 
        .hz_exmem_alu_ovf(exmem_alu_ovf_out), .hz_alu_ovf_wb(alu_ovf_wb), .hz_alu_ovf_arch(flag_ovf_q_w), .hz_alu_zero_pre(alu_zero_pre), 
        .hz_exmem_alu_zero(exmem_alu_zero_out), .hz_alu_zero_wb(alu_zero_wb), .hz_alu_zero_arch(flag_zero_q_w), .hz_readReg2_id(readReg2_id), 
        .hz_rf_r2_id(rf_ReadData2), .hz_alu_pre(alu_pre), .hz_exmem_alu(exmem_alu_out), .hz_memwb_alu(memwb_alu_out), .hz_memwb_mem(memwb_mem_out),
        .hz_forwarded_neg_to_id(forwarded_neg_to_id), .hz_forwarded_ovf_to_id(forwarded_ovf_to_id), 
        .hz_forwarded_zero_to_id(forwarded_zero_to_id), .hz_forwarded_r2_val(forwarded_r2_val), .hz_forwarded_r2_sel(forwarded_r2_sel)
    );

    // ID/REG stage
    wire branch_taken_id; wire [63:0] branch_target_id;
    id_stage idst(
        .clk(clk), .instr(instr_id), .pc_in(pc_id_pc), .wb_WriteData(wb_write_data), .wb_WriteRegister(rd_memwb), .wb_RegWrite(memwb_RegWrite),
        .flag_neg_in(forwarded_neg_to_id), .flag_ovf_in(forwarded_ovf_to_id), .flag_zero_in(forwarded_zero_to_id),
        .forwarded_r2(forwarded_r2_val), .forwarded_r2_sel(forwarded_r2_sel),
        .rf_r1(rf_ReadData1), .rf_r2(rf_ReadData2), .rd(rd_id), .rn(rn_id), .rm(rm_id), .readReg2(readReg2_id), .imm12(imm12_id), 
        .imm19(imm19_id), .imm26(imm26_id), .imm9(imm9_id), .shamt(shamt_id), .imm_selected(imm_selected_id), 
        .op_sel(op_sel_id), .branch_taken_out(branch_taken_id), .branch_target_out(branch_target_id), .Reg2Loc(cu_Reg2Loc), .ALUSrc(cu_ALUSrc), .MemToReg(cu_MemToReg), 
        .RegWrite(cu_RegWrite), .MemWrite(cu_MemWrite), .UncondBr(cu_UncondBr), .Branch(cu_Branch), .ALUOp(cu_ALUOp)
    );

    // ID/EX register instance 
    id_ex_reg idex(
        .clk(clk), .reset(rst), .rf_r1_in(rf_ReadData1), .rf_r2_in(rf_ReadData2), .imm_in(imm_selected_id), .pc_in(pc_id_pc), 
        .pc_plus4_in(pc_plus4_id), .rd_in(rd_id), .rn_in(rn_id), .rm_in(rm_id), .readReg2_in(readReg2_id), 
        .imm19_in(imm19_id), .imm26_in(imm26_id), .op_sel_in(op_sel_id), .ALUOp_in(cu_ALUOp), .ALUSrc_in(cu_ALUSrc), 
        .Reg2Loc_in(cu_Reg2Loc), .MemToReg_in(cu_MemToReg), .RegWrite_in(cu_RegWrite), .MemWrite_in(cu_MemWrite), 
        .UncondBr_in(cu_UncondBr), .Branch_in(cu_Branch), .rf_r1_out(rf_r1_ex), .rf_r2_out(rf_r2_ex), .imm_out(imm_ex), 
        .pc_out(pc_ex), .pc_plus4_out(pc4_ex), .rd_out(rd_ex), .rn_out(rn_ex), .rm_out(rm_ex), .readReg2_out(readReg2_ex), 
        .imm19_out(imm19_ex), .imm26_out(imm26_ex), .op_sel_out(op_sel_ex), .ALUOp_out(ALUOp_ex), .ALUSrc_out(ALUSrc_ex), 
        .Reg2Loc_out(Reg2Loc_ex), .MemToReg_out(MemToReg_ex), .RegWrite_out(RegWrite_ex), .MemWrite_out(MemWrite_ex), 
        .UncondBr_out(UncondBr_ex), .Branch_out(Branch_ex)
    );

    // EXE stage
    exe_stage exst(
        .clk(clk), .rf_r1_ex(rf_r1_ex), .rf_r2_ex(rf_r2_ex), .imm_ex(imm_ex), .rn_ex(rn_ex), .readReg2_ex(readReg2_ex),
        .ALUOp_ex(ALUOp_ex), .ALUSrc_ex(ALUSrc_ex), .op_sel(op_sel_ex), .rd_exmem_in(rd_exmem), .rd_memwb_in(rd_memwb), .exmem_RegWrite_in(exmem_RegWrite),
        .memwb_RegWrite_in(memwb_RegWrite), .exmem_MemToReg_in(exmem_MemToReg), .memwb_MemToReg_in(MemToReg_wb), .exmem_alu_in(exmem_alu_out),
        .memwb_alu_in(memwb_alu_out), .memwb_mem_in(memwb_mem_out), .alu_out_pre(alu_pre), .write_data_pre(write_data_pre),
        .alu_neg_pre(alu_neg_pre), .alu_zero_pre(alu_zero_pre), .alu_ovf_pre(alu_ovf_pre), .alu_carry_pre(alu_carry_pre)
    );

    // instantiate EX/MEM register
    ex_mem_reg exmem_reg_inst(
        .clk(clk), .reset(rst), .alu_out_in(alu_pre), .write_data_in(write_data_pre), .pc_in(pc_ex), .pc_plus4_in(pc4_ex),
        .rd_in(rd_ex), .imm19_in(imm19_ex), .imm26_in(imm26_ex), .MemToReg_in(MemToReg_ex), .RegWrite_in(RegWrite_ex),
        .MemWrite_in(MemWrite_ex), .op_sel_in(op_sel_ex), .alu_neg_in(alu_neg_pre), .alu_zero_in(alu_zero_pre),
        .alu_ovf_in(alu_ovf_pre), .alu_carry_in(alu_carry_pre), .alu_out_out(exmem_alu_out), 
        .write_data_out(exmem_write_data_out), .pc_out(exmem_pc_out), .pc_plus4_out(exmem_pc4_out), .rd_out(rd_exmem), 
        .imm19_out(exmem_imm19_out), .imm26_out(exmem_imm26_out), .MemToReg_out(exmem_MemToReg), .RegWrite_out(exmem_RegWrite),
        .MemWrite_out(exmem_MemWrite), .op_sel_out(exmem_op_out), .alu_neg_out(exmem_alu_neg_out), .alu_zero_out(exmem_alu_zero_out),
        .alu_ovf_out(exmem_alu_ovf_out), .alu_carry_out(exmem_alu_carry_out)
    );

    // Memory stage
    wire [63:0] mem_out_mem;
    wire [3:0] mem_size = 4'd8;
    mem_stage ms(
        .clk(clk), .alu_out(exmem_alu_out), .write_data_in(exmem_write_data_out), .mem_we(exmem_MemWrite), .mem_re(exmem_MemToReg), .mem_size(mem_size), .mem_out(mem_out_mem)
    );

    // MEM/WB register inputs (write-data and pc) - outputs declared earlier
    mem_wb_reg memwb(
        .clk(clk), .reset(rst), .mem_out_in(mem_out_mem), .alu_out_in(exmem_alu_out), .write_data_in(exmem_write_data_out), 
        .pc_in(exmem_pc_out), .pc_plus4_in(exmem_pc4_out), .rd_in(rd_exmem), .imm19_in(exmem_imm19_out), 
        .imm26_in(exmem_imm26_out), .MemToReg_in(exmem_MemToReg), .RegWrite_in(exmem_RegWrite), 
        .op_sel_in(exmem_op_out), .alu_neg_in(exmem_alu_neg_out), .alu_zero_in(exmem_alu_zero_out), 
        .alu_ovf_in(exmem_alu_ovf_out), .alu_carry_in(exmem_alu_carry_out), .mem_out_out(memwb_mem_out), 
        .alu_out_out(memwb_alu_out), .write_data_out(memwb_write_data), .pc_out(memwb_pc), .pc_plus4_out(memwb_pc4), 
        .rd_out(rd_memwb), .imm19_out(memwb_imm19), .imm26_out(memwb_imm26), .MemToReg_out(MemToReg_wb), 
        .RegWrite_out(memwb_RegWrite), .op_sel_out(op_sel_wb), .alu_neg_out(alu_neg_wb), .alu_zero_out(alu_zero_wb), 
        .alu_ovf_out(alu_ovf_wb), .alu_carry_out(alu_carry_wb)
    );

    // WB stage: writeback mux and writeback stage register
    write_stage ws( 
        .clk(clk), .pc_out(memwb_pc), .pc_plus4(memwb_pc4), .alu_out(memwb_alu_out), .mem_out(memwb_mem_out), .rf_r2(memwb_write_data), 
        .op_sel(op_sel_wb), .imm26(), .imm19(), .rd(rd_memwb), .alu_neg(alu_neg_wb), .alu_zero(alu_zero_wb), 
        .alu_ovf(alu_ovf_wb), .alu_carry(alu_carry_wb), .MemToReg(MemToReg_wb), .UncondBr(), .Branch(), .write_data(wb_write_data), .pc_next(),
        .flag_neg_q(flag_neg_q_w), .flag_zero_q(flag_zero_q_w), .flag_ovf_q(flag_ovf_q_w), .flag_carry_q(flag_carry_q_w)
    );

    // PC update logic with branch decision from ID stage
    wire branch_taken_id_n; not1 n_btn_id(.out(branch_taken_id_n), .in0(branch_taken_id));
    mux2_1_64 pc_mux(.in0(pc_plus4_if), .in1(branch_target_id), .sel(branch_taken_id), .sel_n(branch_taken_id_n), .out(pc_in));
endmodule