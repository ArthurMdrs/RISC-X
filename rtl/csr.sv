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
// Design Name:    Control and Status Registers                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RISC-X Control and Status Registers (CSRs).                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module csr import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Ports for CSR read/modify instructions
    input  csr_addr_t      csr_addr_i,
    input  logic    [31:0] csr_wdata_i,
    input  csr_operation_t csr_op_i,
    output logic    [31:0] csr_rdata_o,
    
    // Initial values of CSRs
    input  logic    [31:0] hartid_i,
    input  logic    [23:0] mtvec_i,
    
    // Output some CSRs
    output logic [31:0] mtvec_o,
    output logic [31:0] mepc_o,
    output logic [ 1:0] mstatus_fs_o,
    
    // Trap handling
    input  logic        save_pc_id_i, // Save ID PC to mepc
    input  logic        save_pc_ex_i, // Save EX PC to mepc
    input  logic [31:0] pc_id_i,
    input  logic [31:0] pc_ex_i,
    input  logic [ 4:0] exception_cause_i,
    input               is_mret_i,

    // Floating-point ports
    input  logic [4:0] fflags_i,
    input  logic       fflags_we_i,
    output logic [2:0] frm_o,

    // 
    input reg_bank_mux_t rd_dst_bank_wb_i,
    input logic          reg_wen_wb_i
);

logic [31:0] csr_wdata_actual;
logic        csr_wen;
logic        set_initial_mtvec;

// Machine ISA Register
logic [31:0] misa;
logic [ 1:0] mxl;
assign mxl = 2'b01;
assign misa = {mxl, 17'b0, ISA_M, 6'h04, ISA_F, 2'b0, ISA_C, 2'b0};

// ID registers
logic [31:0] mvendorid; // Machine Vendor ID Register
logic [31:0] marchid;   // Machine Architecture ID Register
logic [31:0] mimpid;    // Machine Implementation ID Register
logic [31:0] mhartid;   // Hart ID Register
assign mvendorid = '0;
assign marchid   = '0;
assign mimpid    = '0;
assign mhartid   = hartid_i;

// Machine Status Registers
mstatus_t mstatus, mstatus_n;
// Track certain types of writes
logic wr_to_f_reg;
logic wr_to_fcsr;
logic wr_to_mstatus;
logic implicit_wr_to_fs;

// Machine Trap-Vector Base-Address Register
logic [31:0] mtvec, mtvec_n;
// Machine Exception Program Counter
logic [31:0] mepc, mepc_n;
// Machine Cause Register
logic [31:0] mcause;
logic        mcause_intr_n;
logic [ 4:0] mcause_code_n;
assign mcause[31]   = 1'b0; // TODO Change this when interrupts are implemented
assign mcause[30:5] = 26'b0;
// Machine Scratch Register
logic [31:0] mscratch, mscratch_n;

// Machine Interrupt Enable Register
logic [31:0] mie, mie_n;

// Adicionei aqui

// FPU Registers
logic [4:0] fflags, fflags_n;
logic [2:0] frm, frm_n;

`ifdef JASPER
`default_nettype none
`endif

// Define read operation
always_comb begin
    case (csr_addr_i)
        CSR_MISA: csr_rdata_o = misa;
        
        CSR_MVENDORID: csr_rdata_o = mvendorid;
        CSR_MARCHID: csr_rdata_o = marchid;
        CSR_MIMPID: csr_rdata_o = mimpid;
        CSR_MHARTID: csr_rdata_o = mhartid;
        
        CSR_MSTATUS: csr_rdata_o = {mstatus.sd, 8'b0, mstatus.tsr, mstatus.tw, mstatus.tvm,
                                    mstatus.mxr, mstatus.sum, mstatus.mprv, mstatus.xs, mstatus.fs,
                                    mstatus.mpp, mstatus.vs, mstatus.spp, mstatus.mpie, mstatus.ube,
                                    mstatus.spie, 1'b0, mstatus.mie, 1'b0, mstatus.sie, 1'b0};
        CSR_MIE: csr_rdata_o = mie;
        CSR_MTVEC: csr_rdata_o = mtvec;
        
        CSR_MEPC: csr_rdata_o = mepc;
        CSR_MCAUSE: csr_rdata_o = mcause;
        CSR_MSCRATCH: csr_rdata_o = mscratch;
        
        CSR_FFLAGS: csr_rdata_o = (ISA_F) ? {27'b0, fflags}:'0;
        CSR_FRM:    csr_rdata_o = (ISA_F) ? {29'b0, frm}:'0;
        CSR_FCSR:   csr_rdata_o = (ISA_F) ? {24'b0, frm, fflags}:'0;

        default: csr_rdata_o = '0;
    endcase
end

// Define next values of CSRs
always_comb begin
    mstatus_n     = mstatus;
    mie_n         = mie;
    mtvec_n       = (set_initial_mtvec) ? ({mtvec_i, 8'b0}) : (mtvec);
    mepc_n        = mepc;
    mcause_intr_n = mcause[31];
    mcause_code_n = mcause[4:0];
    mscratch_n    = mscratch;

    fflags_n = fflags;
    frm_n    = frm;
    
    wr_to_fcsr = 1'b0;
    wr_to_mstatus = 1'b0;

    // Deal with direct writes by CSR instructions
    if (csr_wen) begin
        case (csr_addr_i)
            CSR_MSTATUS: begin
                // mstatus_n.sie  = csr_wdata_actual[ 1];
                // mstatus_n.mie  = csr_wdata_actual[ 3];
                // mstatus_n.spie = csr_wdata_actual[ 5];
                // mstatus_n.ube  = csr_wdata_actual[ 6];
                // mstatus_n.mpie = csr_wdata_actual[ 7];
                // mstatus_n.spp  = csr_wdata_actual[ 8];
                // mstatus_n.vs   = csr_wdata_actual[10: 9];
                mstatus_n.mpp  = csr_wdata_actual[12:11];
                mstatus_n.fs   = (ISA_F) ? (csr_wdata_actual[14:13]) : (FS_OFF);
                // mstatus_n.xs   = csr_wdata_actual[16:15];
                // mstatus_n.mprv = csr_wdata_actual[17];
                // mstatus_n.sum  = csr_wdata_actual[18];
                // mstatus_n.mxr  = csr_wdata_actual[19];
                // mstatus_n.tvm  = csr_wdata_actual[20];
                // mstatus_n.tw   = csr_wdata_actual[21];
                // mstatus_n.tsr  = csr_wdata_actual[22];
                // mstatus_n.sd   = csr_wdata_actual[31];
                wr_to_mstatus = 1'b1;
            end
            CSR_MIE: begin
                mie_n = csr_wdata_actual;
            end
            CSR_MTVEC: begin
                mtvec_n = {csr_wdata_actual[31:8], 8'b0};
            end
            CSR_MEPC: begin
                if (ISA_C) mepc_n = {csr_wdata_actual[31:1], 1'b0};
                else       mepc_n = {csr_wdata_actual[31:2], 2'b0};
            end
            CSR_MCAUSE: begin
                // mcause_intr_n = csr_wdata_actual[31]; // TODO Change this when interrupts are implemented
                mcause_code_n = csr_wdata_actual[4:0];
            end
            CSR_MSCRATCH: begin
                mscratch_n = csr_wdata_actual;
            end

            CSR_FFLAGS: begin
                fflags_n = (ISA_F) ? (csr_wdata_actual[4:0]) : ('0);
                wr_to_fcsr = 1'b1;
            end
            CSR_FRM: begin
                frm_n = (ISA_F) ? (csr_wdata_actual[2:0]) : ('0);
                wr_to_fcsr = 1'b1;
            end
            CSR_FCSR: begin
                fflags_n = (ISA_F) ? (csr_wdata_actual[4:0]) : ('0);
                frm_n    = (ISA_F) ? (csr_wdata_actual[7:5]) : ('0);
                wr_to_fcsr = 1'b1;
            end

        endcase
    end
    
    if (ISA_F) begin
        wr_to_f_reg = reg_wen_wb_i && (rd_dst_bank_wb_i == F_REG);
        // F status field implicit update
        // Can happen because: 
        // - write to f GPR (unless we're writing to mstatus)
        // - write to fflags/frm/fcsr (explicit or implicit)
        implicit_wr_to_fs = (wr_to_f_reg && !wr_to_mstatus) || wr_to_fcsr || fflags_we_i;
        if (implicit_wr_to_fs) begin
            mstatus_n.fs = FS_DIRTY;
        end
        // fflags implicit update
        if (fflags_we_i) begin
            fflags_n = fflags_i | fflags;
        end
    end
    
    // State dirty field indicates if either fs, vs or xs are dirty
    mstatus_n.sd = (mstatus_n.fs == FS_DIRTY);
    
    // Save PC to mepc when traps occur
    unique case (1'b1)
        save_pc_ex_i: mepc_n = pc_ex_i;
        save_pc_id_i: mepc_n = pc_id_i;
        default: ;
    endcase
    // Save cause of exception
    if (save_pc_ex_i || save_pc_id_i) begin
        mcause_code_n = exception_cause_i;
    end
    
    // TODO: implement implicit write to mstatus when mret is executed
    // mret instruction
    if (is_mret_i) begin
        mstatus_n.mie = mstatus.mpie;
        mstatus_n.mpie = 1'b1;
        mstatus_n.mpp  = PRIV_LVL_M;
    end
end

// Update CSR values with next values
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        set_initial_mtvec <= '1;
        mstatus <= '0;
        mstatus.mpp <= PRIV_LVL_M;
        mie  <= '0;
        mtvec <= '0;
        mepc  <= '0;
        // mcause[31] <= '0;
        mcause[4:0] <= '0;
        mscratch <= '0;

        // Adicionei aqui
        fflags <= '0;
        frm <= '0;
    end
    else begin
        set_initial_mtvec <= '0;
        mstatus <= mstatus_n;
        mie  <= mie_n;
        mtvec <= mtvec_n;
        mepc  <= mepc_n;
        // mcause[31] <= mcause_intr_n;
        mcause[4:0] <= mcause_code_n;
        mscratch <= mscratch_n;

        // Adicionei aqui
        // if(ISA_F) begin
            fflags <= fflags_n;
            frm <= frm_n;
        // end
    end
end

// Determine actual wdata
always_comb begin
    csr_wdata_actual = csr_wdata_i;
    csr_wen    = 1'b1;

    case (csr_op_i)
        CSR_WRITE: csr_wdata_actual = csr_wdata_i;
        CSR_SET:   csr_wdata_actual = csr_wdata_i | csr_rdata_o;
        CSR_CLEAR: csr_wdata_actual = (~csr_wdata_i) & csr_rdata_o;
        CSR_READ: begin
            csr_wdata_actual = csr_wdata_i;
            csr_wen    = 1'b0;
        end
    endcase
end

// Output some CSRs
assign frm_o = (ISA_F) ? frm : '0;
assign mtvec_o = mtvec;
// assign mepc_o = mepc;
// Output next value of mepc to account for writes followed by xRET 
assign mepc_o = mepc_n;

assign mstatus_fs_o = mstatus.fs;


`ifdef SVA_ON
    
    // Can't have mret at the same time as other traps
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) !(is_mret_i && (save_pc_ex_i || save_pc_id_i)));
    // Can't have explicit and implicit fflags write at the same time
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) !(fflags_we_i && (csr_wen && (csr_addr_i == CSR_FFLAGS || csr_addr_i == CSR_FCSR))));
    
`endif

`ifdef JASPER
`default_nettype wire
`endif

endmodule