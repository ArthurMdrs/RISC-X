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
    input  alu_operation_t alu_operation_id_i,
    input  logic [ 4:0]    rd_addr_id_i,
    input  logic           mem_wen_id_i,
    input  data_type_t     mem_data_type_id_i,
    input  logic           mem_sign_extend_id_i,
    input  logic           reg_alu_wen_id_i,
    input  logic           reg_mem_wen_id_i,
    input  logic [31:0]    pc_id_i,
    input  pc_source_t     pc_source_id_i,
    input  logic           is_branch_id_i,
    input  logic [31:0]    alu_operand_1_id_i,
    input  logic [31:0]    alu_operand_2_id_i,
    input  logic [31:0]    mem_wdata_id_i,
    input  logic [31:0]    branch_target_id_i,
    input  logic           valid_id_i,
    input  logic           csr_access_id_i,
    input  csr_operation_t csr_op_id_i,
    input  logic [2:0]     roundmode_i,
    input  logic [3:0]     fpu_op_i,
    input  logic           fpu_op_mod_i,
    input  logic           fpu_req_i,
    input  logic           alu_fpu_sel,
    
    // Output to MEM stage
    output logic [ 4:0] rd_addr_ex_o,
    output logic [31:0] alu_result_ex_o,
    output logic        mem_wen_ex_o,
    output data_type_t  mem_data_type_ex_o,
    output logic        mem_sign_extend_ex_o,
    output logic [31:0] mem_wdata_ex_o,
    output logic        reg_alu_wen_ex_o,
    output logic        reg_mem_wen_ex_o,
    output logic        valid_ex_o,
    
    // Output to controller
    // output logic instr_addr_misaligned_ex_o,
    output logic apu_gnt_o,
    output logic apu_rvalid_o,
    
    // Output to CSRs
    output logic [31:0]    pc_ex_o,
    output csr_addr_t      csr_addr_ex_o,
    output logic [31:0]    csr_wdata_ex_o,
    output csr_operation_t csr_op_ex_o,
    output logic           csr_access_ex_o,
    output logic           csr_apu_rflags_o,
    
    // Input from CSRs
    input  logic        csr_access_ex_i,
    input  logic [31:0] csr_rdata_ex_i,
    
    // Control inputs
    input  logic stall_ex_i,
    input  logic flush_ex_i
);

//// FPU Parameters ////

import fpnew_pkg;

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
        '{default: FPU_ADDMUL_LAT}, // ADDMUL
        '{default: C_LAT_DIVSQRT},  // DIVSQRT
        '{default: FPU_OTHERS_LAT}, // NONCOMP
        '{default: FPU_OTHERS_LAT}  // CONV
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

localparam fpnew_pkg::divsqrt_unit_t DIV_SQRT_SEL = TH32;
localparam TRUE_SIMD_CLASS  = 0;
localparam ENABLE_SIMD_MASK = 0;


//// End FPU Parameters ////


///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

logic [2:0][31:0] apu_operands_i;

alu_operation_t alu_operation_ex;
logic [31:0]    alu_operand_1_ex, alu_operand_2_ex;
logic [31:0]    alu_result_ex;

logic is_branch_ex;

logic instr_addr_misaligned_ex;
logic exception_ex;

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_ex_o         <= '0;
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
                alu_operation_ex     <= alu_operation_id_i;
                alu_operand_1_ex     <= alu_operand_1_id_i;
                alu_operand_2_ex     <= alu_operand_2_id_i;
                mem_wen_ex_o         <= mem_wen_id_i;
                mem_data_type_ex_o   <= mem_data_type_id_i;
                mem_sign_extend_ex_o <= mem_sign_extend_id_i;
                mem_wdata_ex_o       <= mem_wdata_id_i;
                reg_alu_wen_ex_o     <= reg_alu_wen_id_i;
                reg_mem_wen_ex_o     <= reg_mem_wen_id_i;
                pc_ex_o              <= pc_id_i;
                pc_source_ex_o       <= pc_source_id_i;
                is_branch_ex         <= is_branch_id_i;
                branch_target_ex_o   <= branch_target_id_i;
                csr_access_ex_o      <= csr_access_id_i;
                if (csr_access_id_i) begin
                    csr_op_ex_o    <= csr_op_id_i;
                    csr_wdata_ex_o <= alu_operand_1_id_i; // wdata is passed through operand 1
                    csr_addr_ex_o  <= csr_addr_t'(alu_operand_2_id_i[11:0]); // addr is passed through operand 2
                end
                valid_ex_o <= valid_id_i;
            end
        end
    end
end

always_comb begin
    case (alu_fpu_sel)
        ULA_SEL: alu_result_ex = alu_result_mux;
        FPU_SEL: alu_result_ex = apu_rdata_o;
        default: alu_result_ex = alu_result_mux;
    endcase
end

alu #(
    .DWIDTH ( 32 )
) alu_inst (
    .res_o       ( alu_result_mux ), 
    .op1_i       ( alu_operand_1_ex ),
    .op2_i       ( alu_operand_2_ex ),
    .operation_i ( alu_operation_ex )
);

generate
    if(ISA_F) begin
        fpnew_top #(
            .Features       (FPU_FEATURES), // Ok
            .Implementation (FPU_IMPLEMENTATION), // Ok
            .DivSqrtSel     (DIV_SQRT_SEL), // Ok
            .TagType        (logic), // Ok
            .TrueSIMDClass  (TRUE_SIMD_CLASS), // Ok
            .EnableSIMDMask (ENABLE_SIMD_MASK) // Ok
        ) fpu_inst (
            .clk_i          (clk_i), // Ok
            .rst_ni         (rst_n_i), // Ok
            // Input signals
            .operands_i     (apu_operands_i), // Ok
            .rnd_mode_i     (roundmode_i), // Decoder Ok
            .op_i           (fpu_op_i), // Decoder Ok
            .op_mod_i       (fpu_op_mod_i), // Decoder Ok
            .src_fmt_i      (fpnew_pkg::FP32), // Ok
            .dst_fmt_i      (fpnew_pkg::FP32), // Ok
            .int_fmt_i      (fpnew_pkg::INT32), // Ok
            .vectorial_op_i (1'b0), // Ok
            .tag_i          (1'b0), // Ok
            .simd_mask_i    (1'b0), // Ok
            // Input Handshake
            .in_valid_i     (apu_req_i), // Ok
            .in_ready_o     (apu_gnt_o), // Ok
            .flush_i        (1'b0), // Ok
            // Output signals
            .result_o       (apu_rdata_o),
            .status_o       (csr_apu_rflags_o), // Ok
            .tag_o          (  /* unused */), // Ok
            // Output handshake
            .out_valid_o    (apu_rvalid_o), // Ok 
            .out_ready_i    (1'b1), // Ok
            // Indication of valid data in flight
            .busy_o         (  /* unused */) // Ok
        );

    end
    else begin
        assign apu_gnt_o = '0;
        assign apu_rvalid_o = '0;
        assign apu_rdata_o '0;
        assign apu_rflags_o = '0;
    end
endgenerate


// Pass CSR rdata through ALU result in case of CSR reads
assign alu_result_ex_o = (csr_access_ex_i) ? (csr_rdata_ex_i) : (alu_result_ex);

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

endmodule