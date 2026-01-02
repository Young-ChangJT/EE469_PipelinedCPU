// Gate-level ALU implementation
`timescale 1ns/10ps

// Basic gate modules with 50ps delay using built-in gates

module not1 (output out, input in0);
    not #50 gate_inst(out, in0);
endmodule

module and2 (output out, input in0, in1);
    and #50 gate_inst(out, in0, in1);
endmodule

module or2 (output out, input in0, in1);
    or #50 gate_inst(out, in0, in1);
endmodule

module xor2 (output out, input in0, in1);
    xor #50 gate_inst(out, in0, in1);
endmodule

module and3 (output out, input in0, in1, in2);
    and #50 gate_inst(out, in0, in1, in2);
endmodule

module and4(output out, input in0, in1, in2, in3);
    and #50 gate_inst(out, in0, in1, in2, in3);
endmodule

module or4(output out, input in0, in1, in2, in3);
    or #50 gate_inst(out, in0, in1, in2, in3);
endmodule

module nor4 (output out, input in0, in1, in2, in3);
    nor #50 gate_inst(out, in0, in1, in2, in3);
endmodule

// 1-bit full adder
module full_adder(
    input in0, in1, cin,
    output sum, cout
    );
    wire w1, w2, w3;
    xor2 x1(.out(w1), .in0(in0), .in1(in1));
    xor2 x2(.out(sum), .in0(w1), .in1(cin));
    and2 a1(.out(w2), .in0(in0), .in1(in1));
    and2 a2(.out(w3), .in0(w1), .in1(cin));
    or2 o1(.out(cout), .in0(w2), .in1(w3));
endmodule

// 64-bit ripple carry adder
module adder64(
    input [63:0] in0, in1,
    input cin,
    output [63:0] sum,
    output cout
    );
    wire [62:0] carry;
    genvar i;
    
    full_adder fa0(.in0(in0[0]), .in1(in1[0]), .cin(cin), .sum(sum[0]), .cout(carry[0]));
    
    generate
        for (i = 1; i < 63; i = i + 1) begin : gen_fa
            full_adder fa(.in0(in0[i]), .in1(in1[i]), .cin(carry[i-1]), .sum(sum[i]), .cout(carry[i]));
        end
    endgenerate
    
    full_adder fa63(.in0(in0[63]), .in1(in1[63]), .cin(carry[62]), .sum(sum[63]), .cout(cout));
endmodule

// 64-bit 2's complement subtractor (A - B = A + ~B + 1)
module subtractor64(
    input [63:0] in0, in1,
    output [63:0] diff,
    output cout
    );
    wire [63:0] b_inv;
    genvar i;
    
    // Invert all bits of in1 to get ~B
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen_inv
            not1 inv(.out(b_inv[i]), .in0(in1[i]));
        end
    endgenerate
    
    // A + (~B) + 1 using the adder with cin=1
    adder64 sub_add(.in0(in0), .in1(b_inv), .cin(1'b1), .sum(diff), .cout(cout));
endmodule

// 64-bit AND operation
module and64(
    input [63:0] in0, in1,
    output [63:0] result
    );
    genvar i;
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen_and
            and2 and_gate(.out(result[i]), .in0(in0[i]), .in1(in1[i]));
        end
    endgenerate
endmodule

// 64-bit OR operation
module or64(
    input [63:0] in0, in1,
    output [63:0] result
    );
    genvar i;
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen_or
            or2 or_gate(.out(result[i]), .in0(in0[i]), .in1(in1[i]));
        end
    endgenerate
endmodule

// 64-bit XOR operation
module xor64(
    input [63:0] in0, in1,
    output [63:0] result
    );
    genvar i;
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen_xor
            xor2 xor_gate(.out(result[i]), .in0(in0[i]), .in1(in1[i]));
        end
    endgenerate
endmodule

// Zero detector (checks if all 64 bits are zero)
module zero_detect(
    input [63:0] data,
    output zero
    );
    wire [15:0] nor_out;
    genvar i;
    
    generate
        for (i = 0; i < 16; i = i + 1) begin : gen_nor
            nor4 nor_gate(.out(nor_out[i]), .in0(data[i*4]), .in1(data[i*4+1]), .in2(data[i*4+2]), .in3(data[i*4+3]));
        end
    endgenerate
    
    wire [3:0] and_out;
    and4 a1(.out(and_out[0]), .in0(nor_out[0]), .in1(nor_out[1]), .in2(nor_out[2]), .in3(nor_out[3]));
    and4 a2(.out(and_out[1]), .in0(nor_out[4]), .in1(nor_out[5]), .in2(nor_out[6]), .in3(nor_out[7]));
    and4 a3(.out(and_out[2]), .in0(nor_out[8]), .in1(nor_out[9]), .in2(nor_out[10]), .in3(nor_out[11]));
    and4 a4(.out(and_out[3]), .in0(nor_out[12]), .in1(nor_out[13]), .in2(nor_out[14]), .in3(nor_out[15]));
    
    and4 final_and(.out(zero), .in0(and_out[0]), .in1(and_out[1]), .in2(and_out[2]), .in3(and_out[3]));
endmodule


// 2-to-1 64-bit structural multiplexer
module mux2_1_64(
    input  [63:0] in0, in1,
    input         sel,
    input         sel_n,
    output [63:0] out
    );
    // sel_n is provided by the caller (precomputed NOT of sel)

    genvar i;
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen2
            wire m0, m1;
            and2 a0(.out(m0), .in0(in0[i]), .in1(sel_n));
            and2 a1(.out(m1), .in0(in1[i]), .in1(sel));
            or2 o(.out(out[i]), .in0(m0), .in1(m1));
        end
    endgenerate
endmodule

// 4-to-1 64-bit structural multiplexer (input_ has 4 elements)
module mux4_1_64(
    input  [63:0] input_ [0:3],
    input  [1:0]  sel,
    input  [1:0]  sel_n,
    output [63:0] out
    );
    // Implement 4-to-1 using three 2-to-1 muxes per bit, forwarding sel_n bits
    // y0 = mux2(input_[0], input_[1], sel[0]) with sel_n[0]
    // y1 = mux2(input_[2], input_[3], sel[0]) with sel_n[0]
    // out = mux2(y0, y1, sel[1]) with sel_n[1]
    wire [63:0] y0, y1;

    // lower pair
    mux2_1_64 lower_pair(.in0(input_[0]), .in1(input_[1]), .sel(sel[0]), .sel_n(sel_n[0]), .out(y0));
    // upper pair
    mux2_1_64 upper_pair(.in0(input_[2]), .in1(input_[3]), .sel(sel[0]), .sel_n(sel_n[0]), .out(y1));
    // final select between pairs
    mux2_1_64 combine(.in0(y0), .in1(y1), .sel(sel[1]), .sel_n(sel_n[1]), .out(out));
endmodule

// 8-to-1 64-bit structural multiplexer built from two 4-to-1 and one 2-to-1
module mux8_1_64(
    input  [63:0] input_ [0:7],
    input  [2:0]  sel,
    input  [2:0]  sel_n,
    output [63:0] out
    );
    wire [63:0] out_lo, out_hi;

    // lower four inputs (0..3) selected by sel[1:0]
    mux4_1_64 lower(.input_(input_[0:3]), .sel(sel[1:0]), .sel_n(sel_n[1:0]), .out(out_lo));
    // upper four inputs (4..7) selected by sel[1:0]
    mux4_1_64 upper(.input_(input_[4:7]), .sel(sel[1:0]), .sel_n(sel_n[1:0]), .out(out_hi));

    // final 2-to-1 mux controlled by sel[2]
    mux2_1_64 final_mux(.in0(out_lo), .in1(out_hi), .sel(sel[2]), .sel_n(sel_n[2]), .out(out));
endmodule

// Main ALU module
module alu(
    input  [63:0] A, B,
    input  [2:0]  cntrl,
    output [63:0] result,
    output negative, zero, overflow, carry_out
    );
    // Internal computation results - direct array approach
    wire [63:0] result_ [0:7];  // 8 elements for 8 operations
    
    wire add_carry, sub_carry;
    wire add_overflow, sub_overflow;
    
    // PASS B operation (000)
    assign result_[0] = B;

    // Logical Shift Right (001)
    shifter lsr_unit(.value(A), .direction(1'b1), .distance(B[5:0]), .result(result_[1]));
    
    // ADD operation (010)
    adder64 adder(.in0(A), .in1(B), .cin(1'b0), .sum(result_[2]), .cout(add_carry));

    // SUBTRACT operation (011)
    subtractor64 subtractor(.in0(A), .in1(B), .diff(result_[3]), .cout(sub_carry));
    
    // Bitwise operations
    and64 and_op(.in0(A), .in1(B), .result(result_[4]));      // AND operation (100)
    or64 or_op(.in0(A), .in1(B), .result(result_[5]));        // OR operation (101)
    xor64 xor_op(.in0(A), .in1(B), .result(result_[6]));      // XOR operation (110)
    
    // Unused operation (111)
    assign result_[7] = 64'b0;

    // Overflow detection for addition
    wire add_sign_same, add_result_diff;
    xor2 add_sign_check(.out(add_sign_same), .in0(A[63]), .in1(B[63]));
    not1 add_sign_inv(.out(add_sign_same_n), .in0(add_sign_same));
    xor2 add_result_check(.out(add_result_diff), .in0(A[63]), .in1(result_[2][63]));
    and2 add_overflow_gate(.out(add_overflow), .in0(add_sign_same_n), .in1(add_result_diff));

    // Overflow detection for subtraction
    wire sub_sign_diff, sub_result_diff;
    xor2 sub_sign_check(.out(sub_sign_diff), .in0(A[63]), .in1(B[63]));
    xor2 sub_result_check(.out(sub_result_diff), .in0(A[63]), .in1(result_[3][63]));
    and2 sub_overflow_gate(.out(sub_overflow), .in0(sub_sign_diff), .in1(sub_result_diff));

    // Instantiate a structural 8-to-1 64-bit multiplexer (single array input)
    // compute inverted control bits once and pass down
    wire [2:0] sel_n;
    not1 n0(.out(sel_n[0]), .in0(cntrl[0]));
    not1 n1(.out(sel_n[1]), .in0(cntrl[1]));
    not1 n2(.out(sel_n[2]), .in0(cntrl[2]));

    mux8_1_64 mux_inst(
        .input_(result_),
        .sel(cntrl),
        .sel_n(sel_n),
        .out(result)
    );
    
    // Flag generation
    assign negative = result[63];
    
    zero_detect zero_det(.data(result), .zero(zero));
    
    // Overflow flag (only for ADD and SUB)
    wire is_add, is_sub;
    
    and3 add_sel(.out(is_add), .in0(sel_n[2]), .in1(cntrl[1]), .in2(sel_n[0])); // 010
    and3 sub_sel(.out(is_sub), .in0(sel_n[2]), .in1(cntrl[1]), .in2(cntrl[0])); // 011
    
    wire add_overflow_en, sub_overflow_en;
    and2 add_overflow_enable(.out(add_overflow_en), .in0(is_add), .in1(add_overflow));
    and2 sub_overflow_enable(.out(sub_overflow_en), .in0(is_sub), .in1(sub_overflow));
    or2 overflow_final(.out(overflow), .in0(add_overflow_en), .in1(sub_overflow_en));
    
    // Carry out flag (only for ADD and SUB)
    wire add_carry_en, sub_carry_en;
    and2 add_carry_enable(.out(add_carry_en), .in0(is_add), .in1(add_carry));
    and2 sub_carry_enable(.out(sub_carry_en), .in0(is_sub), .in1(sub_carry));
    or2 carry_final(.out(carry_out), .in0(add_carry_en), .in1(sub_carry_en)); 
endmodule