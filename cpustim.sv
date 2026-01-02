`timescale 1ns/10ps

module cpustim();
    parameter ClockDelay = 200000;  // 200ns for very long gate-level path (IR + decode + ALU + write)
    logic clk;

    // Instantiate CPU (it uses the `instructmem` BENCHMARK define inside instructmem.sv)
    cpu dut(.clk(clk));

    initial begin
        clk <= 0;
        forever #(ClockDelay/2) clk <= ~clk;
    end

    // Initialize PC to 0 at start of simulation
    initial begin
        // Force PC register to 0 before first clock edge
        force dut.is0.pc_reg.q = 64'h0;
        // Hold for two rising edges so PC=0 for the first two cycles
        @(posedge clk);
        @(posedge clk);
        release dut.is0.pc_reg.q;
        $display("[cpustim] PC held at 0 for two cycles; released at time %0t", $time);
    end

    initial begin
        // monitor key signals each clock cycle
        $display("Time | PC | Instr | RegWrite | rd | ALU_OUT | MEM_OUT | RF_R1 | RF_R2 | WRITE_DATA");
        forever begin
            @(posedge clk);
            $display("%0t | %h | %h | %1h | %02h | %h | %h | %h | %h | %h",
                $time,
                dut.pc_out,
                dut.instr,
                dut.RegWrite,
                dut.rd,
                dut.alu_out,
                dut.mem_out,
                dut.rf_r1,
                dut.rf_r2,
                dut.write_data
            );
        end
    end

    initial begin
        // Monitor register file contents after each clock to verify writes
        $display("\n=== Register File Contents Monitor ===");
        forever begin
            @(posedge clk);
            #100; // Wait 100ps after clock edge for registers to settle
            $display("Time %0t | X0=%h X1=%h X2=%h X3=%h X4=%h X5=%h X6=%h X7=%h",
                $time,
                dut.rfs.rf.registers[0],
                dut.rfs.rf.registers[1],
                dut.rfs.rf.registers[2],
                dut.rfs.rf.registers[3],
                dut.rfs.rf.registers[4],
                dut.rfs.rf.registers[5],
                dut.rfs.rf.registers[6],
                dut.rfs.rf.registers[7]
            );
        end
    end

    initial begin
        // Run long enough for benchmark to complete
        # (ClockDelay * 20);
        $display("Simulation timeout reached; stopping.");
        $stop;
    end
endmodule
