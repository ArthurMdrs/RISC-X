// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    Core wrapper                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Wrapper for RISC-X core that includes the interfaces used  //
//                 in the UVM testbench (except clock and reset interface, we //
//                 pass only the clock and reset signals).                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module core_wrapper #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // clknrst_if if_clknrst,
    bad_uvc_if if_instr_bad_uvc,
    bad_uvc_if if_data_bad_uvc,
    obi_if     if_instr_obi,
    rvvi_if    if_rvvi,
    
    input  logic [31:0] hartid_i,
    input  logic [23:0] mtvec_i,
    input  logic [29:0] boot_addr_i
);

import core_pkg::*;

// RVFI signals
`RVFI_WIRES

// wire clk_i   = if_clknrst.clk  ;
// wire rst_n_i = if_clknrst.rst_n;

core #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) core_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),

    // Bad data interface
    .dmem_rdata_i ( if_data_bad_uvc.rdata ),
    .dmem_wdata_o ( if_data_bad_uvc.wdata ),
    .dmem_addr_o  ( if_data_bad_uvc.addr ),
    .dmem_wen_o   ( if_data_bad_uvc.we ),
    .dmem_ben_o   ( if_data_bad_uvc.be ),
    
    // Bad instr interface
    // .imem_rdata_i ( if_instr_bad_uvc.rdata ),
    // .imem_addr_o  ( if_instr_bad_uvc.addr ),
    
    // OBI instr interface
    .insn_obi_req_o     ( if_instr_obi.req ),
    .insn_obi_gnt_i     ( if_instr_obi.gnt ),
    .insn_obi_addr_o    ( if_instr_obi.addr ),
    .insn_obi_we_o      ( if_instr_obi.we ),
    .insn_obi_be_o      ( if_instr_obi.be ),
    .insn_obi_wdata_o   ( if_instr_obi.wdata ),
    .insn_obi_rvalid_i  ( if_instr_obi.rvalid ),
    .insn_obi_rready_o  ( if_instr_obi.rready ),
    .insn_obi_rdata_i   ( if_instr_obi.rdata ),
    
    .hartid_i    ( hartid_i ),
    .mtvec_i     ( mtvec_i ),
    .boot_addr_i ( boot_addr_i )
);

// Tie-offs
assign if_instr_bad_uvc.wdata = '0;
assign if_instr_bad_uvc.we    = '0;
assign if_instr_bad_uvc.be    = '1;



`include "rvfi_inst.sv"



// DRIVE RVVI

assign if_rvvi.clk = clk_i;
assign if_rvvi.valid = rvfi_valid;
assign if_rvvi.order = rvfi_order;

assign if_rvvi.insn = rvfi_insn;
assign if_rvvi.trap = rvfi_trap;
assign if_rvvi.debug_mode = '0;

// Program counter
assign if_rvvi.pc_rdata = rvfi_pc_rdata;

// X Registers
logic [31:0][31:0] x_wdata;   // X write data value
logic [31:0]       x_wb   ;   // X data writeback (change) flag
always_comb begin
    foreach(if_rvvi.x_wdata[i]) begin
        x_wdata[i] = '0;
        x_wb[i]    = '0;
    end
    if (rvfi_rd_addr != '0) begin
        x_wdata[rvfi_rd_addr] = rvfi_rd_wdata;
        x_wb[rvfi_rd_addr]    = '1;
    end
end
assign if_rvvi.x_wdata = x_wdata;
assign if_rvvi.x_wb    = x_wb;

// F Registers
assign if_rvvi.f_wdata = '{default:'0};
assign if_rvvi.f_wb    = '{default:'0};


// V Registers
// assign if_rvvi.v_wdata = '{default:'0};
// assign if_rvvi.v_wb    = '{default:'0};

// Control and Status Registers
logic [4095:0][31:0] csr_wdata;   // CSR write data value
logic [4095:0]       csr_wb   ;   // CSR data writeback (change) flag
always_comb begin
    foreach(if_rvvi.csr[i]) begin
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
        endcase
    end
end
assign if_rvvi.csr    = csr_wdata;
assign if_rvvi.csr_wb = csr_wb;

// Atomic Memory Control
// assign if_rvvi.lrsc_cancel = '0;

// Optional
assign if_rvvi.pc_wdata = rvfi_pc_wdata;
assign if_rvvi.intr = rvfi_intr;
assign if_rvvi.halt = rvfi_halt;
assign if_rvvi.ixl = rvfi_ixl;
assign if_rvvi.mode = rvfi_mode;

endmodule

