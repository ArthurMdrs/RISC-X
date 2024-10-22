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
// Design Name:    RVFI Driver                                                //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Drives RVFI signals.                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module rvfi import core_pkg::*; #(
    parameter  int FLEN = 32,
    localparam int NRET = `RISCV_FORMAL_NRET
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Input from IF stage
    input  logic         valid_if,
    input  logic         stall_if,
    input  logic [31:0]  pc_if,
    input  next_pc_mux_t next_pc_mux,
    
    // Input from ID stage
    input  logic          valid_id,
    input  logic          stall_id,
    input  logic          flush_id,
    input  logic          trap_id,
    input  logic [31:0]   instr_id,
    input  logic          illegal_instr_id,
    input  alu_source_1_t alu_source_1_id,
    input  alu_source_2_t alu_source_2_id,
    input  alu_source_3_t alu_source_3_id,
    input  logic [ 4:0]   rs1_addr_id,
    input  logic [ 4:0]   rs2_addr_id,
    input  logic [ 4:0]   rs3_addr_id,
    input  reg_bank_mux_t rs1_src_bank_id,
    input  reg_bank_mux_t rs2_src_bank_id,
    input  reg_bank_mux_t rs3_src_bank_id,
    input  logic          rs1_is_used_id,
    input  logic          rs2_is_used_id,
    input  logic          rs3_is_used_id,
    input  logic [31:0]   rs1_or_fwd_id,
    input  logic [31:0]   rs2_or_fwd_id,
    input  logic [31:0]   rs3_or_fwd_id,
    input  logic [31:0]   pc_id,
    input  pc_source_t    pc_source_id,
    input  logic [31:0]   jump_target_id,
    input  logic          mem_wen_id,
    input  logic          is_mret_id,
    
    // Input from EX stage
    input  logic           valid_ex,
    input  logic           stall_ex,
    input  logic           flush_ex,
    input  logic           trap_ex,
    input  logic [31:0]    branch_target_ex,
    input  logic           branch_decision_ex,
    input  logic [31:0]    csr_wdata_ex,
    input  logic [31:0]    csr_rdata_ex,
    input  csr_operation_t csr_op_ex,
    
    // Input from MEM stage
    input  logic        valid_mem,
    input  logic        stall_mem,
    input  logic        flush_mem,
    // input  logic [31:0] dmem_wdata_o,
    // input  logic [31:0] dmem_addr_o,
    // input  logic        dmem_wen_o,
    // input  logic [ 3:0] dmem_ben_o,
    
    // input  logic        data_obi_req,
    input  logic        mem_req_mem,
    input  logic [31:0] data_obi_addr,
    input  logic        data_obi_we,
    input  logic [ 3:0] data_obi_be,
    input  logic [31:0] data_obi_wdata,
    
    // Input from WB stage
    input  logic          flush_wb,
    input  logic [ 4:0]   rd_addr_wb,
    input  reg_bank_mux_t rd_dst_bank_wb,
    input  logic          reg_wen_wb,
    input  logic [31:0]   reg_wdata_wb,
    input  logic [31:0]   mem_rdata_wb,
    
    // Input from CSR
    input  logic [31:0] misa,
    input  mstatus_t    mstatus,
    input  mstatus_t    mstatus_n,
    // input  logic        implicit_wr_to_fs,
    input  logic        wr_to_f_reg,
    input  logic        wr_to_mstatus,
    input  logic        wr_to_fcsr,
    input  logic        fpu_fflags_we_ex,
    input  logic [ 4:0] fpu_fflags_ex,
    input  csr_addr_t   csr_addr,
    
    `RVFI_OUTPUTS,
    
    output [NRET *    5 - 1 : 0] rvfi_frs1_addr,
    output [NRET *    5 - 1 : 0] rvfi_frs2_addr,
    output [NRET *    5 - 1 : 0] rvfi_frs3_addr,
    output [NRET *    5 - 1 : 0] rvfi_frd_addr,
    // output [NRET        - 1 : 0] rvfi_frs1_rvalid,
    // output [NRET        - 1 : 0] rvfi_frs2_rvalid,
    // output [NRET        - 1 : 0] rvfi_frs3_rvalid,
    output [NRET        - 1 : 0] rvfi_frd_wvalid,
    output [NRET * FLEN - 1 : 0] rvfi_frs1_rdata,
    output [NRET * FLEN - 1 : 0] rvfi_frs2_rdata,
    output [NRET * FLEN - 1 : 0] rvfi_frs3_rdata,
    output [NRET * FLEN - 1 : 0] rvfi_frd_wdata
);

logic        intr_if;

// logic        rvfi_valid_id;
logic        intr_id;

// logic        rvfi_valid_ex;
logic [31:0] instr_ex;
logic        rvfi_trap_ex;
logic        intr_ex;
logic [ 4:0] rs1_addr_ex , rs2_addr_ex;
logic [31:0] rs1_rdata_ex, rs2_rdata_ex;
logic [ 4:0] frs1_addr_ex , frs2_addr_ex , frs3_addr_ex;
logic [31:0] frs1_rdata_ex, frs2_rdata_ex, frs3_rdata_ex;
logic [31:0] pc_ex, pc_n_ex;

// logic        rvfi_valid_mem;
logic [31:0] instr_mem;
logic        trap_mem;
logic        intr_mem;
logic [ 4:0] rs1_addr_mem , rs2_addr_mem;
logic [31:0] rs1_rdata_mem, rs2_rdata_mem;
logic [ 4:0] frs1_addr_mem , frs2_addr_mem , frs3_addr_mem;
logic [31:0] frs1_rdata_mem, frs2_rdata_mem, frs3_rdata_mem;
logic [31:0] pc_mem, pc_n_mem;
logic [31:0] csr_wdata_mem, csr_rdata_mem;
logic        csr_wen_mem;

logic        rvfi_valid_wb;
logic [63:0] order_wb;
logic [31:0] instr_wb;
logic        trap_wb;
logic        intr_wb;
logic [ 4:0] rs1_addr_wb, rs2_addr_wb;
logic [31:0] rs1_rdata_wb, rs2_rdata_wb;
logic [ 4:0] frs1_addr_wb , frs2_addr_wb , frs3_addr_wb;
logic [31:0] frs1_rdata_wb, frs2_rdata_wb, frs3_rdata_wb;
logic [31:0] pc_wb, pc_n_wb;
logic [31:0] mem_addr_wb;
logic [ 3:0] mem_wmask_wb, mem_rmask_wb;
logic [31:0] mem_wdata_wb;//, mem_rdata_wb;
logic [31:0] csr_wdata_wb, csr_rdata_wb;
logic        csr_wen_wb;

logic [31:0] csr_mstatus_wdata_ex, csr_mstatus_rdata_ex;
logic        csr_mstatus_wen_ex;
logic [31:0] csr_mstatus_wdata_mem, csr_mstatus_rdata_mem;
logic        csr_mstatus_wen_mem;
logic [31:0] csr_mstatus_wdata_wb, csr_mstatus_rdata_wb;
logic        csr_mstatus_wen_wb;

`ifdef JASPER
`default_nettype none
`endif

///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION FETCH         ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers ->IF
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        intr_if <= '0;
    end else begin
        if (!stall_if) begin
            intr_if <= (next_pc_mux == NPC_EXCEPTION);
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION DECODE        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers IF->ID
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // rvfi_valid_id <= '0;
        intr_id <= '0;
    end else begin
        if (!stall_id) begin
            // Insert bubble if flushing is needed
            if (flush_id) begin
                // rvfi_valid_id <= 1'b0;
                intr_id <= '0;
            end
            else begin
                // rvfi_valid_id <= 1'b1;
                intr_id <= intr_if;
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // rvfi_valid_ex <= '0;
        instr_ex      <= '0;
        rvfi_trap_ex  <= '0;
        intr_ex       <= '0;
        rs1_addr_ex   <= '0;
        rs2_addr_ex   <= '0;
        rs1_rdata_ex  <= '0;
        rs2_rdata_ex  <= '0;
        frs1_addr_ex  <= '0;
        frs2_addr_ex  <= '0;
        frs3_addr_ex  <= '0;
        frs1_rdata_ex <= '0;
        frs2_rdata_ex <= '0;
        frs3_rdata_ex <= '0;
        pc_ex         <= '0;
        pc_n_ex       <= '0;
    end else begin
        if (!stall_ex) begin
            // instr_ex     <= instr_id;
            instr_ex     <= (instr_id[1:0] == 2'b11) ? (instr_id) : ({16'b0, instr_id[15:0]});
            rvfi_trap_ex <= trap_id && !stall_id && !branch_decision_ex;
            intr_ex      <= intr_id;
            // TODO: use signal rs1_is_used from decoder (when it's implemented)
            if ((rs1_src_bank_id == X_REG) && ((alu_source_1_id == ALU_SCR1_RS1) || (pc_source_id == PC_JALR))) begin
                rs1_addr_ex  <= rs1_addr_id;
                rs1_rdata_ex <= rs1_or_fwd_id;
            end else begin
                rs1_addr_ex  <= '0;
                rs1_rdata_ex <= '0;
            end
            if ((rs2_src_bank_id == X_REG) && ((alu_source_2_id == ALU_SCR2_RS2) || mem_wen_id)) begin
                rs2_addr_ex  <= rs2_addr_id;
                rs2_rdata_ex <= rs2_or_fwd_id;
            end else begin
                rs2_addr_ex  <= '0;
                rs2_rdata_ex <= '0;
            end
            // FP registers
            if ((rs1_src_bank_id == F_REG) && ((alu_source_1_id == ALU_SCR1_RS1) || (pc_source_id == PC_JALR))) begin
                frs1_addr_ex  <= rs1_addr_id;
                frs1_rdata_ex <= rs1_or_fwd_id;
            end else begin
                frs1_addr_ex  <= '0;
                frs1_rdata_ex <= '0;
            end
            if ((rs2_src_bank_id == F_REG) && ((alu_source_2_id == ALU_SCR2_RS2) || mem_wen_id)) begin
                frs2_addr_ex  <= rs2_addr_id;
                frs2_rdata_ex <= rs2_or_fwd_id;
            end else begin
                frs2_addr_ex  <= '0;
                frs2_rdata_ex <= '0;
            end
            if ((rs3_src_bank_id == F_REG) && rs3_is_used_id) begin
                frs3_addr_ex  <= rs3_addr_id;
                frs3_rdata_ex <= rs3_or_fwd_id;
            end else begin
                frs3_addr_ex  <= '0;
                frs3_rdata_ex <= '0;
            end
            pc_ex        <= pc_id;
            // pc_n_ex <= (pc_source_id inside {PC_JAL, PC_JALR}) ? (jump_target_id) : (pc_if);
            // Insert bubble if flushing is needed
            if (flush_ex) begin
                pc_n_ex       <= '0;
            end
            else begin
                pc_n_ex <= (pc_source_id inside {PC_JAL, PC_JALR}) ? (jump_target_id) : (pc_if);
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // rvfi_valid_mem <= '0;
        instr_mem      <= '0;
        trap_mem       <= '0;
        intr_mem       <= '0;
        rs1_addr_mem   <= '0;
        rs2_addr_mem   <= '0;
        rs1_rdata_mem  <= '0;
        rs2_rdata_mem  <= '0;
        frs1_addr_mem  <= '0;
        frs2_addr_mem  <= '0;
        frs3_addr_mem  <= '0;
        frs1_rdata_mem <= '0;
        frs2_rdata_mem <= '0;
        frs3_rdata_mem <= '0;
        pc_mem         <= '0;
        pc_n_mem       <= '0;
        csr_wdata_mem  <= '0;
        csr_rdata_mem  <= '0;
        csr_wen_mem    <= '0;
    end else begin
        if (!stall_mem) begin
            instr_mem      <= instr_ex;
            // trap_mem <= rvfi_trap_ex || (trap_ex && !stall_ex); // Moved to if(flush)
            intr_mem <= intr_ex;
            rs1_addr_mem   <= rs1_addr_ex;
            rs2_addr_mem   <= rs2_addr_ex;
            rs1_rdata_mem  <= rs1_rdata_ex;
            rs2_rdata_mem  <= rs2_rdata_ex;
            frs1_addr_mem  <= frs1_addr_ex;
            frs2_addr_mem  <= frs2_addr_ex;
            frs3_addr_mem  <= frs3_addr_ex;
            frs1_rdata_mem <= frs1_rdata_ex;
            frs2_rdata_mem <= frs2_rdata_ex;
            frs3_rdata_mem <= frs3_rdata_ex;
            pc_mem   <= pc_ex;
            // pc_n_mem <= (branch_decision_ex) ? (branch_target_ex) : (pc_n_ex);
            // Insert bubble if flushing is needed
            if (flush_mem) begin
                trap_mem <= '0;
                pc_n_mem       <= '0;    
                csr_wdata_mem  <= '0;
                csr_rdata_mem  <= '0;
                csr_wen_mem    <= '0;
            end
            else begin
                trap_mem <= rvfi_trap_ex || (trap_ex && !stall_ex);
                pc_n_mem       <= (branch_decision_ex) ? (branch_target_ex) : (pc_n_ex);
                csr_wdata_mem  <= csr_wdata_ex;
                csr_rdata_mem  <= csr_rdata_ex;
                csr_wen_mem    <= (csr_op_ex != CSR_READ);
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers MEM->WB
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rvfi_valid_wb <= '0;
        order_wb      <= '0;
        instr_wb      <= '0;
        trap_wb       <= '0;
        intr_wb       <= '0;
        rs1_addr_wb   <= '0;
        rs2_addr_wb   <= '0;
        rs1_rdata_wb  <= '0;
        rs2_rdata_wb  <= '0;
        frs1_addr_wb  <= '0;
        frs2_addr_wb  <= '0;
        frs3_addr_wb  <= '0;
        frs1_rdata_wb <= '0;
        frs2_rdata_wb <= '0;
        frs3_rdata_wb <= '0;
        pc_wb         <= '0;
        pc_n_wb       <= '0;
        mem_addr_wb   <= '0;
        mem_rmask_wb  <= '0;
        mem_wmask_wb  <= '0;
        mem_wdata_wb  <= '0;
        csr_wdata_wb  <= '0;
        csr_rdata_wb  <= '0;
        csr_wen_wb    <= '0;
    end else begin
        order_wb <= order_wb + {63'b0, rvfi_valid};
        instr_wb <= instr_mem;
        trap_wb  <= trap_mem;
        intr_wb  <= intr_mem;
        pc_wb    <= pc_mem;
        // pc_n_wb  <= pc_n_mem;
        rs1_addr_wb   <= rs1_addr_mem;
        rs2_addr_wb   <= rs2_addr_mem;
        rs1_rdata_wb  <= rs1_rdata_mem;
        rs2_rdata_wb  <= rs2_rdata_mem;
        frs1_addr_wb  <= frs1_addr_mem;
        frs2_addr_wb  <= frs2_addr_mem;
        frs3_addr_wb  <= frs3_addr_mem;
        frs1_rdata_wb <= frs1_rdata_mem;
        frs2_rdata_wb <= frs2_rdata_mem;
        frs3_rdata_wb <= frs3_rdata_mem;
        // Insert bubble if flushing is needed
        if (flush_wb) begin
            rvfi_valid_wb <= '0;
            pc_n_wb       <= '0;
            mem_addr_wb   <= '0;
            mem_rmask_wb  <= '0;
            mem_wmask_wb  <= '0;
            mem_wdata_wb  <= '0;
            csr_wdata_wb  <= '0;
            csr_rdata_wb  <= '0;
            csr_wen_wb    <= '0;
        end
        else begin
            // rvfi_valid_wb <= rvfi_valid_mem;
            rvfi_valid_wb <= valid_mem;
            pc_n_wb       <= pc_n_mem;
            mem_addr_wb   <= data_obi_addr;
            if (mem_req_mem) begin
                mem_rmask_wb  <= (!data_obi_we) ? (data_obi_be) : ('0);
                mem_wmask_wb  <= ( data_obi_we) ? (data_obi_be) : ('0);
            end
            else begin
                mem_rmask_wb <= '0;
                mem_wmask_wb <= '0;
            end
            mem_wdata_wb  <= data_obi_wdata;
            csr_wdata_wb  <= csr_wdata_mem;
            csr_rdata_wb  <= csr_rdata_mem;
            csr_wen_wb    <= csr_wen_mem;
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
////////////////////////             RVFI             /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Instruction Metadata
assign rvfi_valid = rvfi_valid_wb || trap_wb;
assign rvfi_order = order_wb;
assign rvfi_insn = instr_wb;
assign rvfi_trap = trap_wb;
assign rvfi_halt = 1'b0;
assign rvfi_intr = intr_wb;
assign rvfi_mode = 2'b11;
assign rvfi_ixl  = 2'b01;

// Integer Register Read/Write
assign rvfi_rs1_addr  = rs1_addr_wb;
assign rvfi_rs1_rdata = rs1_rdata_wb;
assign rvfi_rs2_addr  = rs2_addr_wb;
assign rvfi_rs2_rdata = rs2_rdata_wb;
assign rvfi_rd_addr   = ((rd_dst_bank_wb == X_REG) && reg_wen_wb) ? (rd_addr_wb) : ('0);
assign rvfi_rd_wdata  = (!rvfi_rd_addr) ? ('0) : (reg_wdata_wb);

// Floating-point Register Read/Write
assign rvfi_frs1_addr  = frs1_addr_wb;
assign rvfi_frs1_rdata = frs1_rdata_wb;
assign rvfi_frs2_addr  = frs2_addr_wb;
assign rvfi_frs2_rdata = frs2_rdata_wb;
assign rvfi_frs3_addr  = frs3_addr_wb;
assign rvfi_frs3_rdata = frs3_rdata_wb;
assign rvfi_frd_addr   = ((rd_dst_bank_wb == F_REG) && reg_wen_wb) ? (rd_addr_wb) : ('0);
assign rvfi_frd_wdata  = reg_wdata_wb;
assign rvfi_frd_wvalid = (rd_dst_bank_wb == F_REG);

// Program Counter
assign rvfi_pc_rdata = pc_wb;
assign rvfi_pc_wdata = pc_n_wb;

// Memory Access
assign rvfi_mem_addr  = mem_addr_wb;
assign rvfi_mem_rmask = mem_rmask_wb;
assign rvfi_mem_rdata = mem_rdata_wb;
assign rvfi_mem_wmask = mem_wmask_wb;
assign rvfi_mem_wdata = mem_wdata_wb;

// misa CSR
// wire [31:0] csr_mask_wb = {32{rvfi_valid_wb}};
wire [31:0] csr_rmask_wb = {32{rvfi_valid_wb}};
wire [31:0] csr_wmask_wb = {32{csr_wen_wb}};
assign rvfi_csr_misa_rmask = '1;
assign rvfi_csr_misa_rdata = misa;
assign rvfi_csr_misa_wmask = csr_wmask_wb;
assign rvfi_csr_misa_wdata = csr_wdata_wb;

`define assign_rvfi_csr(name) \
assign rvfi_csr_``name``_rmask = csr_rmask_wb; \
assign rvfi_csr_``name``_rdata = csr_rdata_wb; \
assign rvfi_csr_``name``_wmask = csr_wmask_wb; \
assign rvfi_csr_``name``_wdata = csr_wdata_wb;

`assign_rvfi_csr(mhartid)
`assign_rvfi_csr(mvendorid)
`assign_rvfi_csr(marchid)
`assign_rvfi_csr(mimpid)

// `assign_rvfi_csr(mstatus)
`assign_rvfi_csr(mie)
`assign_rvfi_csr(mtvec)

`assign_rvfi_csr(mepc)
`assign_rvfi_csr(mcause)
`assign_rvfi_csr(mscratch)

`assign_rvfi_csr(fcsr)
`assign_rvfi_csr(fflags)
`assign_rvfi_csr(frm)

///////////////////////////////////////////////////////////////////////////////
////////////////////       CONTROL/STATUS REGISTERS       /////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        csr_mstatus_wdata_ex <= '0;
        csr_mstatus_rdata_ex <= '0;
        csr_mstatus_wen_ex   <= '0;
    end else begin
        if (!stall_ex) begin
            csr_mstatus_rdata_ex <= {mstatus.sd, 8'b0, mstatus.tsr, mstatus.tw, mstatus.tvm,
                                     mstatus.mxr, mstatus.sum, mstatus.mprv, mstatus.xs, mstatus.fs,
                                     mstatus.mpp, mstatus.vs, mstatus.spp, mstatus.mpie, mstatus.ube,
                                     mstatus.spie, 1'b0, mstatus.mie, 1'b0, mstatus.sie, 1'b0};
            if (is_mret_id) begin
                csr_mstatus_wen_ex   <= 1'b1;
                csr_mstatus_wdata_ex <= {mstatus_n.sd, 8'b0, mstatus_n.tsr, mstatus_n.tw, mstatus_n.tvm,
                                         mstatus_n.mxr, mstatus_n.sum, mstatus_n.mprv, mstatus_n.xs, mstatus_n.fs,
                                         mstatus_n.mpp, mstatus_n.vs, mstatus_n.spp, mstatus_n.mpie, mstatus_n.ube,
                                         mstatus_n.spie, 1'b0, mstatus_n.mie, 1'b0, mstatus_n.sie, 1'b0};
            end
            else begin
                csr_mstatus_wen_ex   <= 1'b0;
            end
            // Insert bubble if flushing is needed
            // if (flush_ex) begin
            // end
            // else begin
            // end
        end
    end
end

// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        csr_mstatus_wdata_mem <= '0;
        csr_mstatus_rdata_mem <= '0;
        csr_mstatus_wen_mem   <= '0;
    end else begin
        // csr_mstatus_rdata_mem <= mstatus;
        // csr_mstatus_wen_mem   <= (mstatus != mstatus_n);
        // csr_mstatus_wdata_mem <= mstatus_n;
        if (!stall_mem) begin
            // csr_mstatus_rdata_mem <= {mstatus.sd, 8'b0, mstatus.tsr, mstatus.tw, mstatus.tvm,
            //                           mstatus.mxr, mstatus.sum, mstatus.mprv, mstatus.xs, mstatus.fs,
            //                           mstatus.mpp, mstatus.vs, mstatus.spp, mstatus.mpie, mstatus.ube,
            //                           mstatus.spie, 1'b0, mstatus.mie, 1'b0, mstatus.sie, 1'b0};
            // csr_mstatus_wen_mem   <= (mstatus != mstatus_n);
            // csr_mstatus_wdata_mem <= {mstatus_n.sd, 8'b0, mstatus_n.tsr, mstatus_n.tw, mstatus_n.tvm,
            //                           mstatus_n.mxr, mstatus_n.sum, mstatus_n.mprv, mstatus_n.xs, mstatus_n.fs,
            //                           mstatus_n.mpp, mstatus_n.vs, mstatus_n.spp, mstatus_n.mpie, mstatus_n.ube,
            //                           mstatus_n.spie, 1'b0, mstatus_n.mie, 1'b0, mstatus_n.sie, 1'b0};
            
            csr_mstatus_rdata_mem <= csr_mstatus_rdata_ex;
            if (csr_op_ex != CSR_READ && csr_addr == CSR_MSTATUS) begin
                // csr_mstatus_rdata_mem <= csr_rdata_ex;
                csr_mstatus_wen_mem   <= 1'b1;
                csr_mstatus_wdata_mem <= csr_wdata_ex;
            end
            else if ((wr_to_f_reg && !wr_to_mstatus) || wr_to_fcsr || (fpu_fflags_we_ex && |fpu_fflags_ex)) begin
                csr_mstatus_wen_mem   <= 1'b1;
                csr_mstatus_wdata_mem <= {mstatus_n.sd, 8'b0, mstatus_n.tsr, mstatus_n.tw, mstatus_n.tvm,
                                          mstatus_n.mxr, mstatus_n.sum, mstatus_n.mprv, mstatus_n.xs, mstatus_n.fs,
                                          mstatus_n.mpp, mstatus_n.vs, mstatus_n.spp, mstatus_n.mpie, mstatus_n.ube,
                                          mstatus_n.spie, 1'b0, mstatus_n.mie, 1'b0, mstatus_n.sie, 1'b0};
            end
            // else if (implicit_wr_to_fs) begin
            //     csr_mstatus_wen_mem   <= 1'b1;
            //     csr_mstatus_wdata_mem <= {mstatus_n.sd, 8'b0, mstatus_n.tsr, mstatus_n.tw, mstatus_n.tvm,
            //                               mstatus_n.mxr, mstatus_n.sum, mstatus_n.mprv, mstatus_n.xs, mstatus_n.fs,
            //                               mstatus_n.mpp, mstatus_n.vs, mstatus_n.spp, mstatus_n.mpie, mstatus_n.ube,
            //                               mstatus_n.spie, 1'b0, mstatus_n.mie, 1'b0, mstatus_n.sie, 1'b0};
            // end
            else begin
                // csr_mstatus_rdata_mem <= csr_mstatus_rdata_ex;
                csr_mstatus_wen_mem   <= csr_mstatus_wen_ex;
                csr_mstatus_wdata_mem <= csr_mstatus_wdata_ex;
            end
            
            // if (flush_mem) begin
            //     csr_mstatus_rdata_mem <= '0;
            //     csr_mstatus_wen_mem   <= '0;    
            //     csr_mstatus_wdata_mem <= '0;
            // end
            // else begin
            //     csr_mstatus_rdata_mem <= mstatus;
            //     csr_mstatus_wen_mem   <= (mstatus != mstatus_n);
            //     csr_mstatus_wdata_mem <= mstatus_n;
            // end
        end
    end
end

// Pipeline registers MEM->WB
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        csr_mstatus_wdata_wb <= '0;
        csr_mstatus_rdata_wb <= '0;
        csr_mstatus_wen_wb   <= '0;
    end else begin
        // if (flush_wb) begin
        //     csr_mstatus_wdata_wb  <= '0;
        //     csr_mstatus_rdata_wb  <= '0;
        //     csr_mstatus_wen_wb    <= '0;
        // end
        // else begin
            csr_mstatus_wdata_wb  <= csr_mstatus_wdata_mem;
            csr_mstatus_rdata_wb  <= csr_mstatus_rdata_mem;
            csr_mstatus_wen_wb    <= csr_mstatus_wen_mem;
        // end
    end
end

assign rvfi_csr_mstatus_rmask = '1;
assign rvfi_csr_mstatus_rdata = csr_mstatus_rdata_wb;
assign rvfi_csr_mstatus_wmask = {32{csr_mstatus_wen_wb}};
assign rvfi_csr_mstatus_wdata = csr_mstatus_wdata_wb;

`ifdef JASPER
`default_nettype wire
`endif

endmodule
