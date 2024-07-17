module wb_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Input from MEM stage
    input  logic [ 4:0] rd_addr_mem_i,
    input  logic [31:0] alu_result_mem_i,
    input  logic [31:0] mem_rdata_mem_i,
    input  logic        reg_alu_wen_mem_i,
    input  logic        reg_mem_wen_mem_i,
    input  logic        valid_mem_i,
    
    // Output to register file
    output logic [31:0] reg_wdata_wb_o,
    output logic        reg_wen_wb_o,
    
    // Output for forwarding
    output logic [ 4:0] rd_addr_wb_o,
    output logic [31:0] alu_result_wb_o,
    output logic [31:0] mem_rdata_wb_o,
    output logic        reg_alu_wen_wb_o,
    output logic        reg_mem_wen_wb_o
    
);

///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers MEM->WB
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_wb_o     <= '0;
        alu_result_wb_o  <= '0;
        mem_rdata_wb_o   <= '0;
        reg_alu_wen_wb_o <= '0;
        reg_mem_wen_wb_o <= '0;
    end else begin
        if (valid_mem_i) begin
            rd_addr_wb_o     <= rd_addr_mem_i;
            alu_result_wb_o  <= alu_result_mem_i;
            mem_rdata_wb_o   <= mem_rdata_mem_i;
            reg_alu_wen_wb_o <= reg_alu_wen_mem_i;
            reg_mem_wen_wb_o <= reg_mem_wen_mem_i;
        end
        // Insert bubble if previous stage wasn't valid
        else begin
            reg_alu_wen_wb_o <= '0;
            reg_mem_wen_wb_o <= '0;
        end
    end
end

// Determine write enable and write data for the register file
always_comb begin
    if (reg_alu_wen_wb_o)
        reg_wdata_wb_o = alu_result_wb_o;
    else if (reg_mem_wen_wb_o)
        reg_wdata_wb_o = mem_rdata_wb_o;
    else
        reg_wdata_wb_o = alu_result_wb_o;
    
    reg_wen_wb_o = reg_alu_wen_wb_o || reg_mem_wen_wb_o;
end

endmodule



/*
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_wb_o         <= '0;
        alu_result_wb_o      <= '0;
        // mem_data_type_wb   <= '0;
        // mem_sign_extend_wb <= '0;
        mem_rdata_wb_o       <= '0;
        reg_alu_wen_wb_o     <= '0;
        reg_mem_wen_wb_o     <= '0;
    end else begin
        rd_addr_wb_o         <= rd_addr_mem;
        alu_result_wb_o      <= alu_result_mem;
        // mem_data_type_wb   <= mem_data_type_mem;
        // mem_sign_extend_wb <= mem_sign_extend_mem;
        // mem_rdata_wb_o       <= dmem_rdata_i;
        mem_rdata_wb_o       <= mem_rdata_mem;
        reg_alu_wen_wb_o     <= reg_alu_wen_mem;
        reg_mem_wen_wb_o     <= reg_mem_wen_mem;
    end
end

// always_comb begin
//     unique case (mem_data_type_wb)
//         BYTE     : begin
//             if (mem_sign_extend_wb)
//                 mem_rdata_ext_wb = {24{mem_rdata_wb_o[7]}, mem_rdata_wb_o[7:0]};
//             else
//                 mem_rdata_ext_wb = {24'b0, mem_rdata_wb_o[7:0]};
//         end
//         HALF_WORD: begin
//             if (mem_sign_extend_wb)
//                 mem_rdata_ext_wb = {16{mem_rdata_wb_o[15]}, mem_rdata_wb_o[15:0]};
//             else
//                 mem_rdata_ext_wb = {16'b0, mem_rdata_wb_o[15:0]};
//         end
//         WORD     : begin
//             mem_rdata_ext_wb = mem_rdata_wb_o;
//         end
//         default: mem_rdata_ext_wb = mem_rdata_wb_o;
//     endcase
// end

// Determine write enable and write data for the register file
always_comb begin
    if (reg_alu_wen_wb_o)
        reg_wdata_wb_o = alu_result_wb_o;
    else if (reg_mem_wen_wb_o)
        // reg_wdata_wb_o = mem_rdata_ext_wb;
        reg_wdata_wb_o = mem_rdata_wb_o;
    else
        // reg_wdata_wb_o = '0;
        reg_wdata_wb_o = alu_result_wb_o;
    
    reg_wen_wb_o = reg_alu_wen_wb_o || reg_mem_wen_wb_o;
end
*/