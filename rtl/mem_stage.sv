module mem_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,

    // Interface with data memory
    input  logic [31:0] dmem_rdata_i,
    output logic [31:0] dmem_wdata_o,
    output logic [31:0] dmem_addr_o,
    output logic        dmem_wen_o,
    output logic  [3:0] dmem_ben_o,
    
    // Input from EX stage
    input  logic [ 4:0] rd_addr_ex_i,
    input  logic [31:0] alu_result_ex_i,
    input  logic        mem_wen_ex_i,
    input  data_type_t  mem_data_type_ex_i,
    input  logic        mem_sign_extend_ex_i,
    input  logic [31:0] mem_wdata_ex_i,
    input  logic        reg_alu_wen_ex_i,
    input  logic        reg_mem_wen_ex_i,
    input  logic        valid_ex_i,
    
    // Output to WB stage
    output logic [ 4:0] rd_addr_mem_o,
    output logic [31:0] alu_result_mem_o,
    output logic [31:0] mem_rdata_mem_o,
    output logic        reg_alu_wen_mem_o,
    output logic        reg_mem_wen_mem_o,
    output logic        valid_mem_o,
    
    // Control inputs
    input  logic stall_mem_i,
    input  logic flush_wb_i
);

///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        mem_wen_mem;
data_type_t  mem_data_type_mem;
logic        mem_sign_extend_mem;
logic [31:0] mem_wdata_mem;


// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_mem_o         <= '0;
        alu_result_mem_o      <= '0;
        mem_wen_mem           <= '0;
        mem_data_type_mem     <= WORD;
        mem_sign_extend_mem   <= '0;
        mem_wdata_mem         <= '0;
        reg_alu_wen_mem_o     <= '0;
        reg_mem_wen_mem_o     <= '0;
    end else begin
        if (!stall_mem_i) begin
            if (valid_ex_i) begin
                rd_addr_mem_o         <= rd_addr_ex_i;
                alu_result_mem_o      <= alu_result_ex_i;
                mem_wen_mem           <= mem_wen_ex_i;
                mem_data_type_mem     <= mem_data_type_ex_i;
                mem_sign_extend_mem   <= mem_sign_extend_ex_i;
                mem_wdata_mem         <= mem_wdata_ex_i;
                reg_alu_wen_mem_o     <= reg_alu_wen_ex_i;
                reg_mem_wen_mem_o     <= reg_mem_wen_ex_i;
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                mem_wen_mem           <= '0;
                reg_alu_wen_mem_o     <= '0;
                reg_mem_wen_mem_o     <= '0;
            end
        end
    end
end

// Data Memory Interface
assign dmem_wdata_o = mem_wdata_mem;
assign dmem_addr_o  = alu_result_mem_o;
assign dmem_wen_o   = mem_wen_mem;

always_comb begin
    unique case (mem_data_type_mem)
        BYTE     : dmem_ben_o = 4'b0001;
        HALF_WORD: dmem_ben_o = 4'b0011;
        WORD     : dmem_ben_o = 4'b1111;
        default: dmem_ben_o = 4'b0000;
    endcase
end

// Sign extend the data read from memory
always_comb begin
    unique case (mem_data_type_mem)
        BYTE     : begin
            if (mem_sign_extend_mem)
                mem_rdata_mem_o = {{24{dmem_rdata_i[7]}}, dmem_rdata_i[7:0]};
            else
                mem_rdata_mem_o = {24'b0, dmem_rdata_i[7:0]};
        end
        HALF_WORD: begin
            if (mem_sign_extend_mem)
                mem_rdata_mem_o = {{16{dmem_rdata_i[15]}}, dmem_rdata_i[15:0]};
            else
                mem_rdata_mem_o = {16'b0, dmem_rdata_i[15:0]};
        end
        WORD     : begin
            mem_rdata_mem_o = dmem_rdata_i;
        end
        default: mem_rdata_mem_o = dmem_rdata_i;
    endcase
end

// Resolve validness. Not valid implies inserting bubble
assign valid_mem_o = !stall_mem_i && !flush_wb_i;

endmodule