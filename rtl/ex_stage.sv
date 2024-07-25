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
    input  pc_source_t     pc_source_id_i,
    input  logic           is_branch_id_i,
    input  logic [31:0]    alu_operand_1_id_i,
    input  logic [31:0]    alu_operand_2_id_i,
    input  logic [31:0]    mem_wdata_id_i,
    input  logic [31:0]    branch_target_id_i,
    input  logic           valid_id_i,
    input  logic           csr_access_id_i,
    input  csr_operation_t csr_op_id_i,
    
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
    
    // Output to CSRs
    output csr_addr_t      csr_addr_ex_o,
    output logic [31:0]    csr_wdata_ex_o,
    output csr_operation_t csr_op_ex_o,
    output logic           csr_access_ex_o,
    
    // Input from CSRs
    input  logic        csr_access_ex_i,
    input  logic [31:0] csr_rdata_ex_i,
    
    // Control inputs
    input  logic stall_ex_i,
    // input  logic flush_mem_i
    input  logic flush_ex_i
);

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

alu_operation_t alu_operation_ex;
logic [31:0]    alu_operand_1_ex, alu_operand_2_ex;
logic [31:0]    alu_result_ex;

logic is_branch_ex;

logic instr_addr_misaligned_ex;
logic exception_ex;
// logic trap_ex_o;

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
            // if (valid_id_i) begin
            //     rd_addr_ex_o         <= rd_addr_id_i;
            //     alu_operation_ex     <= alu_operation_id_i;
            //     alu_operand_1_ex     <= alu_operand_1_id_i;
            //     alu_operand_2_ex     <= alu_operand_2_id_i;
            //     mem_wen_ex_o         <= mem_wen_id_i;
            //     mem_data_type_ex_o   <= mem_data_type_id_i;
            //     mem_sign_extend_ex_o <= mem_sign_extend_id_i;
            //     mem_wdata_ex_o       <= mem_wdata_id_i;
            //     reg_alu_wen_ex_o     <= reg_alu_wen_id_i;
            //     reg_mem_wen_ex_o     <= reg_mem_wen_id_i;
            //     pc_source_ex_o       <= pc_source_id_i;
            //     is_branch_ex         <= is_branch_id_i;
            //     branch_target_ex_o   <= branch_target_id_i;
            //     csr_access_ex_o      <= csr_access_id_i;
            //     if (csr_access_id_i) begin
            //         csr_op_ex_o    <= csr_op_id_i;
            //         csr_wdata_ex_o <= alu_operand_1_id_i; // wdata is passed through operand 1
            //         csr_addr_ex_o  <= csr_addr_t'(alu_operand_2_id_i[11:0]); // addr is passed through operand 2
            //     end
            // end
            // // Insert bubble if previous stage wasn't valid
            // else begin
            //     mem_wen_ex_o     <= '0;
            //     reg_alu_wen_ex_o <= '0;
            //     reg_mem_wen_ex_o <= '0;
            //     is_branch_ex     <= '0;
            //     csr_op_ex_o      <= CSR_READ;
            //     csr_access_ex_o  <= '0;
            // end
            
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
                pc_source_ex_o       <= pc_source_id_i;
                is_branch_ex         <= is_branch_id_i;
                branch_target_ex_o   <= branch_target_id_i;
                csr_access_ex_o      <= csr_access_id_i;
                if (csr_access_id_i) begin
                    csr_op_ex_o    <= csr_op_id_i;
                    csr_wdata_ex_o <= alu_operand_1_id_i; // wdata is passed through operand 1
                    csr_addr_ex_o  <= csr_addr_t'(alu_operand_2_id_i[11:0]); // addr is passed through operand 2
                end
                // valid_ex_o <= 1'b1;
                valid_ex_o <= valid_id_i;
            end
        end
    end
end

alu #(
    .DWIDTH ( 32 )
) alu_inst (
	.res_o       ( alu_result_ex ), 
	.op1_i       ( alu_operand_1_ex ),
	.op2_i       ( alu_operand_2_ex ),
	.operation_i ( alu_operation_ex )
);

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

// Resolve validness. Not valid implies inserting bubble
// assign valid_ex_o = !stall_ex_i && !flush_mem_i && !trap_ex_o;

endmodule