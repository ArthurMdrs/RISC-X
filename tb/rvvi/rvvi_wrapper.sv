module rvvi_wrapper #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,

    // Interface with data memory
    input  logic [31:0] dmem_rdata_i,
    output logic [31:0] dmem_wdata_o,
    output logic [31:0] dmem_addr_o,
    output logic        dmem_wen_o,
    output logic  [3:0] dmem_ben_o,

    // Interface with instruction memory
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o,
    
    // Hart ID, defined by system
    input  logic [31:0] hartid_i,
    // mtvec initial address, defined by system
    input  logic [23:0] mtvec_i, // 24 upper bits, 256-byte aligned
    // Boot addr (first fetch)
    input  logic [29:0] boot_addr_i, // 30 upper bits, word aligned
    
    // RVVI interface
    rvviTrace rvvi
);

import core_pkg::*;

// RVFI signals
`RVFI_WIRES

// logic [ 4:0] rvfi_frs1_addr;
// logic [ 4:0] rvfi_frs2_addr;
// logic [ 4:0] rvfi_frs3_addr;
logic [ 4:0] rvfi_frd_addr;
// logic rvfi_frs1_rvalid;
// logic rvfi_frs2_rvalid;
// logic rvfi_frs3_rvalid;
logic        rvfi_frd_wvalid;
// logic [31:0] rvfi_frs1_rdata;
// logic [31:0] rvfi_frs2_rdata;
// logic [31:0] rvfi_frs3_rdata;
logic [31:0] rvfi_frd_wdata;

core #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) core_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    .dmem_rdata_i ( dmem_rdata_i ),
    .dmem_wdata_o ( dmem_wdata_o ),
    .dmem_addr_o  ( dmem_addr_o ),
    .dmem_wen_o   ( dmem_wen_o ),
    .dmem_ben_o   ( dmem_ben_o ),
    
    .imem_rdata_i ( imem_rdata_i ),
    .imem_addr_o  ( imem_addr_o ),
    
    .hartid_i    ( hartid_i ),
    .mtvec_i     ( mtvec_i ),
    .boot_addr_i ( boot_addr_i )
);

`include "rvfi_inst.sv"



// DRIVE RVVI

assign rvvi.clk = clk_i;
assign rvvi.valid[0][0] = rvfi_valid;
assign rvvi.order[0][0] = rvfi_order;

assign rvvi.insn[0][0] = rvfi_insn;
assign rvvi.trap[0][0] = rvfi_trap;
assign rvvi.debug_mode[0][0] = '0;

// Program counter
assign rvvi.pc_rdata[0][0] = rvfi_pc_rdata;

// X Registers
logic [31:0][31:0] x_wdata;   // X write data value
logic [31:0]       x_wb   ;   // X data writeback (change) flag
always_comb begin
    foreach(rvvi.x_wb[0][0][i]) begin
        x_wdata[i] = '0;
        x_wb[i]    = '0;
    end
    if (rvfi_rd_addr != '0) begin
        x_wdata[rvfi_rd_addr] = rvfi_rd_wdata;
        x_wb[rvfi_rd_addr]    = '1;
    end
end
assign rvvi.x_wdata[0][0] = x_wdata;
assign rvvi.x_wb[0][0]    = x_wb;

// F Registers
// assign rvvi.f_wdata[0][0] = '{default:'0};
// assign rvvi.f_wb[0][0]    = '{default:'0};
logic [31:0][31:0] f_wdata;   // F write data value
logic [31:0]       f_wb   ;   // F data writeback (change) flag
always_comb begin
    foreach(rvvi.f_wb[0][0][i]) begin
        f_wdata[i] = '0;
        f_wb[i]    = '0;
    end
    if (rvfi_frd_wvalid) begin
        f_wdata[rvfi_frd_addr] = rvfi_frd_wdata;
        f_wb[rvfi_frd_addr]    = '1;
    end
end
assign rvvi.f_wdata[0][0] = f_wdata;
assign rvvi.f_wb[0][0]    = f_wb;


// V Registers
assign rvvi.v_wdata[0][0] = '{default:'0};
assign rvvi.v_wb[0][0]    = '{default:'0};

// Control and Status Registers
logic [4095:0][31:0] csr_wdata;   // CSR write data value
logic [4095:0]       csr_wb   ;   // CSR data writeback (change) flag
always_comb begin
    foreach(rvvi.csr[0][0][i]) begin
        csr_wdata[i] = '0;
        csr_wb[i]    = '0;
    end
    if(rvfi_inst.csr_wen_wb) begin
        case(1'b1)
            (rvfi_insn[31:20]==CSR_MISA): begin
                csr_wdata[CSR_MISA] = rvfi_csr_misa_wdata;
                csr_wb[CSR_MISA]    = 1'b1;
            end
            
            (rvfi_insn[31:20]==CSR_MVENDORID): begin
                csr_wdata[CSR_MVENDORID] = rvfi_csr_mvendorid_wdata;
                csr_wb[CSR_MVENDORID]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MARCHID): begin
                csr_wdata[CSR_MARCHID] = rvfi_csr_marchid_wdata;
                csr_wb[CSR_MARCHID]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MIMPID): begin
                csr_wdata[CSR_MIMPID] = rvfi_csr_mimpid_wdata;
                csr_wb[CSR_MIMPID]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MHARTID): begin
                csr_wdata[CSR_MHARTID] = rvfi_csr_mhartid_wdata;
                csr_wb[CSR_MHARTID]    = 1'b1;
            end
            
            (rvfi_insn[31:20]==CSR_MSTATUS): begin
                csr_wdata[CSR_MSTATUS] = rvfi_csr_mstatus_wdata;
                csr_wb[CSR_MSTATUS]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MIE): begin
                csr_wdata[CSR_MIE] = rvfi_csr_mie_wdata;
                csr_wb[CSR_MIE]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MTVEC): begin
                csr_wdata[CSR_MTVEC] = rvfi_csr_mtvec_wdata;
                csr_wb[CSR_MTVEC]    = 1'b1;
            end
            
            (rvfi_insn[31:20]==CSR_MEPC): begin
                csr_wdata[CSR_MEPC] = rvfi_csr_mepc_wdata;
                csr_wb[CSR_MEPC]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MCAUSE): begin
                csr_wdata[CSR_MCAUSE] = rvfi_csr_mcause_wdata;
                csr_wb[CSR_MCAUSE]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_MSCRATCH): begin
                csr_wdata[CSR_MSCRATCH] = rvfi_csr_mscratch_wdata;
                csr_wb[CSR_MSCRATCH]    = 1'b1;
            end
            
            (rvfi_insn[31:20]==CSR_FFLAGS): begin
                csr_wdata[CSR_FFLAGS] = rvfi_csr_fflags_wdata;
                csr_wb[CSR_FFLAGS]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_FRM): begin
                csr_wdata[CSR_FRM] = rvfi_csr_frm_wdata;
                csr_wb[CSR_FRM]    = 1'b1;
            end
            (rvfi_insn[31:20]==CSR_FCSR): begin
                csr_wdata[CSR_FCSR] = rvfi_csr_fcsr_wdata;
                csr_wb[CSR_FCSR]    = 1'b1;
            end
        endcase
    end
end
assign rvvi.csr[0][0]    = csr_wdata;
assign rvvi.csr_wb[0][0] = csr_wb;

// Atomic Memory Control
assign rvvi.lrsc_cancel[0][0] = '0;

// Optional
assign rvvi.pc_wdata[0][0] = rvfi_pc_wdata;
assign rvvi.intr[0][0] = rvfi_intr;
assign rvvi.halt[0][0] = rvfi_halt;
assign rvvi.ixl[0][0] = rvfi_ixl;
assign rvvi.mode[0][0] = rvfi_mode;

endmodule

