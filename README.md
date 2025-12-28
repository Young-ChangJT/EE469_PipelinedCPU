# 64-bit ARM Pipelined Processor

Implementation of a 64-bit ARM-compatible pipelined CPU core in SystemVerilog, featuring a 5-stage pipeline with data forwarding, load/branch delay slots, and full integration of modular components including register file, ALU, and data/instruction memories.

## Key Features

- **Pipelining**: 5-stage pipeline (Fetch, Decode, Execute, Memory, Writeback) with 1 delay slot after `LDUR`, `B`, `B.LT`, and `CBZ` instructions.  
- **Data Forwarding**: Comprehensive forwarding logic from ALU and memory stages to ALU, branch comparator, and memory address generation units; handles register `X31` zeroing and variable register encoding across instructions.  
- **Instruction Set**: Supports core ARM instructions including `ADDI`, `ADDS`, `AND`, `B`, `B.LT`, `CBZ`, `EOR`, `LDUR`, `LSR`, `STUR`, `SUBS`.  
- **Modular Design**: Integrates register file (32×64-bit entries), 64-bit ALU (arithmetic/logic/shift ops), single-cycle CPU datapath, and provided instruction/data memories.  

### Pipeline Overview

- Stages: Fetch → Decode → Execute → Memory → Writeback  
- Forwarding paths from EX/MEM stages to:
  - ALU inputs  
  - Branch comparison logic  
  - Memory address generation  

The design correctly handles forwarding-branch interactions, non-register-writing instructions, and ensures zero-extension/sign-extension for immediates where required.

## Testing & Demo

- Verified functionality via provided instruction sequences and all prior benchmarks.  
- Top-level testbench with waveform capture for:
  - Registers  
  - Program counter (PC)  
  - Flags  
  - Instruction/data memories  
  - Clock and reset  
- Clock period tuned for clear visibility of single-cycle behavior in simulation waveforms.  

## Build & Simulate

Clone the repository and use ModelSim (or compatible simulator):

vlog *.sv instructmem.sv datamem.sv math.sv
vsim -do testbench.do

All modules from prior designs (e.g., register file, ALU) are required and are assumed to be fully functional and present in the project.




