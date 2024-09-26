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
//                 Ewerton Cordeiro -                                         //
//                 Davi Medeiros -                                            //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Contains ALUs.                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module ex_stage import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Output to IF stage
    output pc_source_t  pc_source_ex_o,
    output logic [31:0] branch_target_ex_o,
    output logic        branch_decision_ex_o,
    output logic        trap_ex_o,
    
    // Input from ID stage
    input  alu_operation_t  alu_operation_id_i,
    input  alu_result_mux_t alu_result_mux_id_i,
    input  logic [ 4:0]     rd_addr_id_i,
    input  reg_bank_mux_t   rd_dst_bank_id_i,
    input  logic            mem_wen_id_i,
    input  data_type_t      mem_data_type_id_i,
    input  logic            mem_sign_extend_id_i,
    input  logic            reg_alu_wen_id_i,
    input  logic            reg_mem_wen_id_i,
    input  logic [31:0]     pc_id_i,
    input  pc_source_t      pc_source_id_i,
    input  logic            is_branch_id_i,
    input  logic [31:0]     alu_operand_1_id_i,
    input  logic [31:0]     alu_operand_2_id_i,
    input  logic [31:0]     alu_operand_3_id_i,
    input  logic [31:0]     mem_wdata_id_i,
    input  logic [31:0]     branch_target_id_i,
    input  logic            valid_id_i,
    input  logic            csr_access_id_i,
    input  csr_operation_t  csr_op_id_i,
    
    // Output to MEM stage
    output logic [ 4:0]   rd_addr_ex_o,
    output reg_bank_mux_t rd_dst_bank_ex_o,
    output logic [31:0]   alu_result_ex_o,
    output logic          mem_wen_ex_o,
    output data_type_t    mem_data_type_ex_o,
    output logic          mem_sign_extend_ex_o,
    output logic [31:0]   mem_wdata_ex_o,
    output logic          reg_alu_wen_ex_o,
    output logic          reg_mem_wen_ex_o,
    output logic          valid_ex_o,
    
    // Output to controller
    // output logic instr_addr_misaligned_ex_o,
    
    // Output to CSRs
    output logic [31:0]    pc_ex_o,
    output csr_addr_t      csr_addr_ex_o,
    output logic [31:0]    csr_wdata_ex_o,
    output csr_operation_t csr_op_ex_o,
    output logic           csr_access_ex_o,
    output logic [ 4:0]    csr_fpu_flags_ex_o,
    
    // Input from CSRs
    input  logic [31:0] csr_rdata_ex_i,
    
    // Control inputs
    input  logic stall_ex_i,
    input  logic flush_ex_i,
    
    // FPU signals
    input  logic [2:0]    fpu_rnd_mode_id_i,
    input  logic [3:0]    fpu_op_id_i,
    input  logic [2:0]    fpu_frm_i,
    input  logic          fpu_op_mod_id_i,
    input  logic          fpu_req_id_i,
    output logic          fpu_gnt_id_o,
    // output logic [31:0]    fpu_result_o,
    // output logic           fpu_rvalid_o,
    output logic          fpu_busy_ex_o
);

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

logic [2:0] [31:0] fpu_operands_i;
logic [31:0]    fpu_result;
logic           fpu_rvalid;
logic           fpu_busy_int;

alu_operation_t alu_operation_ex;
logic [31:0]    alu_operand_1_ex, alu_operand_2_ex;
logic [31:0]    alu_result_ex;
logic [31:0]    basic_alu_result;
alu_result_mux_t alu_result_mux_ex;

logic is_branch_ex;

logic instr_addr_misaligned_ex;
logic exception_ex;

`ifdef JASPER
`default_nettype none
`endif

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_ex_o         <= '0;
        rd_dst_bank_ex_o     <= X_REG;
        alu_operation_ex     <= ALU_ADD;
        alu_operand_1_ex     <= '0;
        alu_operand_2_ex     <= '0;
        mem_wen_ex_o         <= '0;
        mem_data_type_ex_o   <= WORD;
        mem_sign_extend_ex_o <= '0;
        mem_wdata_ex_o       <= '0;
        reg_alu_wen_ex_o     <= '0;
        reg_mem_wen_ex_o     <= '0;
        pc_ex_o              <= '0;
        pc_source_ex_o       <= PC_NEXT;
        is_branch_ex         <= '0;
        branch_target_ex_o   <= '0;
        csr_access_ex_o      <= '0;
        csr_op_ex_o          <= CSR_READ;
        csr_wdata_ex_o       <= '0;
        csr_addr_ex_o        <= CSR_USTATUS;
        valid_ex_o           <= '0;
        alu_result_mux_ex    <= BASIC_ALU_RESULT;
    end else begin
        if (!stall_ex_i) begin
            // Insert bubble if flushing is needed
            if (flush_ex_i) begin
                mem_wen_ex_o     <= '0;
                reg_alu_wen_ex_o <= '0;
                reg_mem_wen_ex_o <= '0;
                is_branch_ex     <= '0;
                csr_op_ex_o      <= CSR_READ;
                csr_access_ex_o  <= '0;
                valid_ex_o       <= 1'b0;
            end
            else begin
                rd_addr_ex_o         <= rd_addr_id_i;
                rd_dst_bank_ex_o     <= rd_dst_bank_id_i;
                alu_operation_ex     <= alu_operation_id_i;
                alu_operand_1_ex     <= alu_operand_1_id_i;
                alu_operand_2_ex     <= alu_operand_2_id_i;
                mem_wen_ex_o         <= mem_wen_id_i;
                mem_data_type_ex_o   <= mem_data_type_id_i;
                mem_sign_extend_ex_o <= mem_sign_extend_id_i;
                mem_wdata_ex_o       <= mem_wdata_id_i; // TODO: pass mem signals only if necessary
                reg_alu_wen_ex_o     <= reg_alu_wen_id_i;
                reg_mem_wen_ex_o     <= reg_mem_wen_id_i;
                pc_ex_o              <= pc_id_i;
                pc_source_ex_o       <= pc_source_id_i;
                is_branch_ex         <= is_branch_id_i;
                branch_target_ex_o   <= branch_target_id_i;
                csr_access_ex_o      <= csr_access_id_i;
                csr_op_ex_o          <= csr_op_id_i;
                if (csr_access_id_i) begin
                    // csr_op_ex_o    <= csr_op_id_i;
                    csr_wdata_ex_o <= alu_operand_1_id_i; // wdata is passed through operand 1
                    csr_addr_ex_o  <= csr_addr_t'(alu_operand_2_id_i[11:0]); // addr is passed through operand 2
                end
                alu_result_mux_ex <= alu_result_mux_id_i;
                valid_ex_o        <= valid_id_i;
            end
        end
    end
end

always_comb begin
    case (alu_result_mux_ex)
        BASIC_ALU_RESULT: alu_result_ex = basic_alu_result;
        FPU_RESULT      : alu_result_ex = fpu_result;
        default: alu_result_ex = basic_alu_result;
    endcase
end

alu #(
    .DWIDTH ( 32 )
) alu_inst (
    .res_o       ( basic_alu_result ), 
    .op1_i       ( alu_operand_1_ex ),
    .op2_i       ( alu_operand_2_ex ),
    .operation_i ( alu_operation_ex )
);

generate
    if(ISA_F) begin
        
        // Number of pipeline stages for Floating-Point ADDition/MULtiplication
        localparam FPU_ADDMUL_LAT = 5;
        // Number of pipeline stages for Floating-Point DIVision/SQuaRe rooT
        localparam FPU_DIVSQRT_LAT = 3;
        // Number of pipeline stages for Floating-Point Non-Computational Operations and Conversions
        localparam FPU_OTHERS_LAT = 2;
        
        // Features (enabled formats, vectors etc.)
        localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
            Width: 32, // Width of the datapath and of the input/output data ports
            EnableVectors: 0, // If set to 1, vectorial execution units will be generated
            EnableNanBox: 0, // Controls whether input value NaN-boxing is enforced
            FpFmtMask: {// FP32, FP64, FP16,  FP8, FP16alt  // If a bit is set, hardware for the corresponding float format is generated
                        1'b1, 1'b0, 1'b0, 1'b0, 1'b0 
                    },
            IntFmtMask: {// INT8, INT16, INT32, INT64 // If a bit is set, hardware for the corresponding int format is generated
                            1'b0,  1'b0,  1'b1,  1'b0
                        }
        };
        
        // Implementation (number of registers etc)
        localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
            // Sets a number of pipeline stages to be inserted into the units per operation group for each format
            // Operation groups: ADDMUL, DIVSQRT, NONCOMP, CONV
            // Formats: FP32, FP64, FP16, FP8, FP16alt
            PipeRegs: '{
                '{default: FPU_ADDMUL_LAT},   // ADDMUL
                '{default: FPU_DIVSQRT_LAT},  // DIVSQRT
                '{default: FPU_OTHERS_LAT},   // NONCOMP
                '{default: FPU_OTHERS_LAT}    // CONV
            },
            // Sets the unit types for the units per operation group for each format
            // Unit types: DISABLED, PARALLEL, MERGED
            UnitTypes: '{
                '{default: fpnew_pkg::MERGED},   // ADDMUL
                '{default: fpnew_pkg::MERGED},   // DIVSQRT
                '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                '{default: fpnew_pkg::MERGED}    // CONV
            },
            PipeConfig: fpnew_pkg::AFTER
        };
        
        localparam fpnew_pkg::divsqrt_unit_t DIV_SQRT_SEL = fpnew_pkg::TH32;
        localparam int unsigned TRUE_SIMD_CLASS  = 0;
        localparam int unsigned ENABLE_SIMD_MASK = 0;
        
        fpnew_pkg::roundmode_e fpu_rnd_mode;
        // fpnew_pkg::roundmode_e fpu_rnd_mode_fpnew;
        assign fpu_rnd_mode = (fpu_rnd_mode_id_i == fpnew_pkg::DYN) ? (fpnew_pkg::roundmode_e'(fpu_frm_i)) : (fpnew_pkg::roundmode_e'(fpu_rnd_mode_id_i));
        fpnew_pkg::operation_e fpu_op;
        assign fpu_op = fpnew_pkg::operation_e'(fpu_op_id_i);
        fpnew_pkg::status_t fpu_flags;
        assign csr_fpu_flags_ex_o = {fpu_flags.NV, fpu_flags.DZ, fpu_flags.OF, fpu_flags.UF, fpu_flags.NX};
        
        assign fpu_operands_i[0] = alu_operand_1_id_i;
        assign fpu_operands_i[1] = alu_operand_2_id_i;
        assign fpu_operands_i[2] = alu_operand_3_id_i;
        
        // assign fpu_rnd_mode_fpnew = (fpu_rnd_mode == 3'b111) ? fpu_frm_i : fpu_rnd_mode;

        fpnew_top #(
            .Features       (FPU_FEATURES),
            .Implementation (FPU_IMPLEMENTATION),
            .DivSqrtSel     (DIV_SQRT_SEL),
            .TagType        (logic),
            .TrueSIMDClass  (TRUE_SIMD_CLASS),
            .EnableSIMDMask (ENABLE_SIMD_MASK)
        ) fpu_inst (
            .clk_i          (clk_i),
            .rst_ni         (rst_n_i),
            // Input signals
            .operands_i     (fpu_operands_i),
            .rnd_mode_i     (fpu_rnd_mode),
            .op_i           (fpu_op),
            .op_mod_i       (fpu_op_mod_id_i),
            .src_fmt_i      (fpnew_pkg::FP32),
            .dst_fmt_i      (fpnew_pkg::FP32),
            .int_fmt_i      (fpnew_pkg::INT32),
            .vectorial_op_i (1'b0),
            .tag_i          (1'b0),
            .simd_mask_i    (1'b0),
            // Input Handshake
            .in_valid_i     (fpu_req_id_i),
            .in_ready_o     (fpu_gnt_id_o),
            .flush_i        (1'b0),
            // Output signals
            .result_o       (fpu_result),
            .status_o       (fpu_flags),
            .tag_o          (/* unused */),
            // Output handshake
            .out_valid_o    (fpu_rvalid), 
            .out_ready_i    (1'b1),
            // Indication of valid data in flight
            .busy_o         (/* unused */)
        );
        
        wire fpu_tr_cnt_up = fpu_req_id_i && fpu_gnt_id_o;
        wire fpu_tr_cnt_dn = fpu_rvalid;
        always_ff @(posedge clk_i, negedge rst_n_i) begin
            if (!rst_n_i) begin
                fpu_busy_int <= 1'b0;
            end else begin
                unique case ({fpu_tr_cnt_up, fpu_tr_cnt_dn})
                    2'b00: fpu_busy_int <= fpu_busy_int; // No  new input tr, no output done
                    2'b01: fpu_busy_int <= 1'b0;         // No  new input tr,    output done
                    2'b10: fpu_busy_int <= 1'b1;         // Got new input tr, no output done
                    2'b11: fpu_busy_int <= 1'b1;         // Got new input tr,    output done
                    default: fpu_busy_int <= 1'b0;
                endcase
            end
        end
        assign fpu_busy_ex_o = fpu_busy_int && !fpu_rvalid;
    end
    else begin
        assign fpu_operands_i = '0;
        assign fpu_gnt_id_o = '0;
        assign fpu_result = '0;
        assign csr_fpu_flags_ex_o = '0;
        assign fpu_rvalid = '0;
        assign fpu_busy_ex_o = '0;
    end
endgenerate

// Pass CSR rdata through ALU result in case of CSR reads
assign alu_result_ex_o = (csr_access_ex_o) ? (csr_rdata_ex_i) : (alu_result_ex);

// Control signal for branches (this will invalidate IF and ID)
assign branch_decision_ex_o = is_branch_ex && alu_result_ex_o[0];

// Taken branch target misaligned exception
always_comb begin
    if (ISA_C) // No such exceptions if compressed instructions are allowed
        instr_addr_misaligned_ex = 1'b0;
    else // If no compressed instructions, target must be 4-byte aligned
        instr_addr_misaligned_ex = branch_target_ex_o[1] && branch_decision_ex_o;
end

// Traps: branch target misaligned
assign exception_ex = instr_addr_misaligned_ex;
assign trap_ex_o = valid_ex_o && exception_ex;

`ifdef JASPER
`default_nettype wire

//(wrapper.rvfi_inst.instr_id[7:0] != 7'h73)
//(wrapper.core_inst.ex_stage_inst.csr_access_id_i == 1'b0 && wrapper.core_inst.ex_stage_inst.csr_op_id_i != 2'b00)
`endif

endmodule