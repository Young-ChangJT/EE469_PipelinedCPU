`timescale 1ns/10ps

module cpu_pipelinedstim();
    parameter ClockDelay = 20000;  // 200ns for very long gate-level path (IR + decode + ALU + write)
    logic clk;
    logic rst;

    // Instantiate CPU (it uses the `instructmem` BENCHMARK define inside instructmem.sv)
    cpu_pipelined dut(.clk(clk), .rst(rst));

    initial begin
        clk <= 0;
        forever #(ClockDelay/2) clk <= ~clk;
    end

    // Drive reset: assert for two cycles at start
    initial begin
        rst <= 1'b1;
        @(posedge clk);
        @(posedge clk);
        rst <= 1'b0;
        $display("[tb] rst released at time %0t", $time);
    end

    // Initialize PC to 0 at start of simulation
    initial begin
        // Force PC register to 0 before first clock edge
        force dut.ifs.pc_reg.q = 64'h0;
        // Hold for two rising edges so PC=0 for the first two cycles
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        release dut.ifs.pc_reg.q;
        $display("[cpustim] PC held at 0 for two cycles; released at time %0t", $time);
    end

    initial begin
        // monitor key signals each clock cycle
        $display("Time | PC | Instr | RegWrite_wb | rd_wb | EX_ALU | MEM_OUT | RF_R1 | RF_R2 | WB_DATA");
        forever begin
            @(posedge clk);
            // Use internal signal names from cpu_pipelined top-level
            $display("%0t | %h | %h | %1b | %02h | %h | %h | %h | %h | %h",
                $time,
                dut.ifs.pc_out,         // IF stage PC
                dut.ifs.instr,         // fetched instruction
                dut.RegWrite_wb,       // RegWrite at WB stage
                dut.rd_wb,             // destination reg at WB
                dut.exmem_alu_out,     // ALU output in EX/MEM (just after EX)
                dut.mem_out_mem,       // memory read output (MEM stage)
                dut.rf_ReadData1,      // regfile read port 1 (ID stage)
                dut.rf_ReadData2,      // regfile read port 2 (ID stage)
                dut.wb_write_data      // final writeback data selected by WB mux
            );
        end
    end

    initial begin
        // Monitor register file contents after each clock to verify writes
        $display("\n=== Register File Contents Monitor ===");
        forever begin
            @(posedge clk);
            #100; // Wait 100ps after clock edge for registers to settle
            $display("Time %0t | X0=%4h X1=%4h X2=%3h X3=%3h X4=%3h X5=%3h X6=%3h X7=%3h X8=%3h X9=%3h X10=%3h X11=%3h X12=%3h X13=%3h X14=%3h X15=%3h X16=%3h X17=%3h X18=%3h X19=%3h X20=%3h X31=%3h",
                $time,
                dut.idst.rf.registers[0],
                dut.idst.rf.registers[1],
                dut.idst.rf.registers[2],
                dut.idst.rf.registers[3],
                dut.idst.rf.registers[4],
                dut.idst.rf.registers[5],
                dut.idst.rf.registers[6],
                dut.idst.rf.registers[7],
                dut.idst.rf.registers[8],
                dut.idst.rf.registers[9],
                dut.idst.rf.registers[10],
                dut.idst.rf.registers[11],
                dut.idst.rf.registers[12],
                dut.idst.rf.registers[13],
                dut.idst.rf.registers[14],
                dut.idst.rf.registers[15],
                dut.idst.rf.registers[16],
                dut.idst.rf.registers[17],
                dut.idst.rf.registers[18],
                dut.idst.rf.registers[19],
                dut.idst.rf.registers[20],
                dut.idst.rf.registers[31],
            );
        end
    end

    initial begin
        // Run long enough for benchmark to complete
        # (ClockDelay * 1800);
        $display("Simulation timeout reached; stopping.");
        $stop;
    end
endmodule
