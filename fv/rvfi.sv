module rvfi import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Input from IF stage
    input  logic        valid_if,
    input  logic [31:0] pc_if,
    
    // Input from ID stage
    input  logic          valid_id,
    input  logic          stall_id,
    input  logic [31:0]   instr_id,
    input  logic          illegal_instr_id,
    input  alu_source_1_t alu_source_1_id,
    input  alu_source_2_t alu_source_2_id,
    input  logic [ 4:0]   rs1_addr_id,
    input  logic [ 4:0]   rs2_addr_id,
    input  logic [31:0]   rs1_or_fwd_id,
    input  logic [31:0]   rs2_or_fwd_id,
    input  logic [31:0]   pc_id,
    input  pc_source_t    pc_source_id,
    input  logic [31:0]   jump_target_id,
    input  logic          mem_wen_id,
    
    // Input from EX stage
    input  logic        valid_ex,
    input  logic        stall_ex,
    input  logic        flush_ex,
    input  logic [31:0] branch_target_ex,
    input  logic        branch_decision_ex,
    input  logic [31:0] csr_wdata_ex,
    input  logic [31:0] csr_rdata_ex,
    
    // Input from MEM stage
    input  logic        valid_mem,
    input  logic        stall_mem,
    input  logic [31:0] dmem_wdata_o,
    input  logic [31:0] dmem_addr_o,
    input  logic        dmem_wen_o,
    input  logic [ 3:0] dmem_ben_o,
    
    // Input from WB stage
    input  logic [ 4:0] rd_addr_wb,
    input  logic        reg_wen_wb,
    input  logic [31:0] reg_wdata_wb,
    input  logic [31:0] mem_rdata_wb,
    
    input  logic [31:0] misa,
    
    `RVFI_OUTPUTS
);

///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION DECODE        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        rvfi_valid_id;

// Pipeline registers IF->ID
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rvfi_valid_id <= '0;
    end else begin
        if (!stall_id) begin
            if (valid_if) begin
                rvfi_valid_id <= 1'b1;
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                rvfi_valid_id <= 1'b0;
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        rvfi_valid_ex;
logic [31:0] instr_ex;
logic        trap_ex;
logic [ 4:0] rs1_addr_ex, rs2_addr_ex;
logic [31:0] rs1_rdata_ex, rs2_rdata_ex;
logic [31:0] pc_ex, pc_n_ex;

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rvfi_valid_ex <= '0;
        instr_ex      <= '0;
        trap_ex       <= '0;
        rs1_addr_ex   <= '0;
        rs2_addr_ex   <= '0;
        rs1_rdata_ex  <= '0;
        rs2_rdata_ex  <= '0;
        pc_ex         <= '0;
        pc_n_ex       <= '0;
    end else begin
        if (!stall_ex) begin
            trap_ex <= (flush_ex) ? ('0) : (illegal_instr_id);
            pc_ex   <= pc_id;
            pc_n_ex <= (pc_source_id inside {PC_JAL, PC_JALR}) ? (jump_target_id) : (pc_if);
            if (valid_id) begin
                rvfi_valid_ex <= rvfi_valid_id;
                instr_ex      <= instr_id;
                // trap_ex       <= illegal_instr_id;
                if ((alu_source_1_id == ALU_SCR1_RS1) || (pc_source_id == PC_JALR)) begin
                    rs1_addr_ex <= rs1_addr_id;
                    rs1_rdata_ex   <= rs1_or_fwd_id;
                end else begin
                    rs1_addr_ex <= '0;
                    rs1_rdata_ex   <= '0;
                end
                if ((alu_source_2_id == ALU_SCR2_RS2) || mem_wen_id) begin
                    rs2_addr_ex <= rs2_addr_id;
                    rs2_rdata_ex   <= rs2_or_fwd_id;
                end else begin
                    rs2_addr_ex <= '0;
                    rs2_rdata_ex   <= '0;
                end
                // pc_ex   <= pc_id;
                // pc_n_ex <= (pc_source_id inside {PC_JAL, PC_JALR}) ? (jump_target_id) : (pc_if);
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                rvfi_valid_ex <= '0;
                instr_ex      <= '0;
                // trap_ex      <= '0;
                rs1_addr_ex   <= '0;
                rs2_addr_ex   <= '0;
                rs1_rdata_ex  <= '0;
                rs2_rdata_ex  <= '0;
                // pc_ex        <= '0;
                // pc_n_ex      <= '0;
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        rvfi_valid_mem;
logic [31:0] instr_mem;
logic        trap_mem;
logic [ 4:0] rs1_addr_mem, rs2_addr_mem;
logic [31:0] rs1_rdata_mem, rs2_rdata_mem;
logic [31:0] pc_mem, pc_n_mem;
logic [31:0] csr_wdata_mem, csr_rdata_mem;

// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rvfi_valid_mem <= '0;
        instr_mem      <= '0;
        trap_mem       <= '0;
        rs1_addr_mem   <= '0;
        rs2_addr_mem   <= '0;
        rs1_rdata_mem  <= '0;
        rs2_rdata_mem  <= '0;
        pc_mem         <= '0;
        pc_n_mem       <= '0;
        csr_wdata_mem  <= '0;
        csr_rdata_mem  <= '0;
    end else begin
        if (!stall_mem) begin
            trap_mem <= trap_ex;
            pc_mem   <= pc_ex;
            pc_n_mem <= (branch_decision_ex) ? (branch_target_ex) : (pc_n_ex);
            if (valid_ex) begin
                rvfi_valid_mem <= rvfi_valid_ex;
                instr_mem      <= instr_ex;
                // trap_mem      <= trap_ex;
                rs1_addr_mem   <= rs1_addr_ex;
                rs2_addr_mem   <= rs2_addr_ex;
                rs1_rdata_mem  <= rs1_rdata_ex;
                rs2_rdata_mem  <= rs2_rdata_ex;
                // pc_mem        <= pc_ex;
                // pc_n_mem      <= (branch_decision_ex) ? (branch_target_ex) : (pc_n_ex);
                csr_wdata_mem  <= csr_wdata_ex;
                csr_rdata_mem  <= csr_wdata_ex;
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                rvfi_valid_mem <= '0;
                instr_mem      <= '0;
                // trap_mem      <= '0;
                rs1_addr_mem   <= '0;
                rs2_addr_mem   <= '0;
                rs1_rdata_mem  <= '0;
                rs2_rdata_mem  <= '0;
                // pc_mem        <= '0;
                // pc_n_mem      <= '0;
                csr_wdata_mem  <= '0;
                csr_rdata_mem  <= '0;
            end
        end
    end
end

///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        rvfi_valid_wb;
logic [63:0] order_wb;
logic [31:0] instr_wb;
logic        trap_wb;
logic [ 4:0] rs1_addr_wb, rs2_addr_wb;
logic [31:0] rs1_rdata_wb, rs2_rdata_wb;
logic [31:0] pc_wb, pc_n_wb;
logic [31:0] mem_addr_wb;
logic [ 3:0] mem_wmask_wb, mem_rmask_wb;
logic [31:0] mem_wdata_wb;//, mem_rdata_wb;
logic [31:0] csr_wdata_wb, csr_rdata_wb;

// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rvfi_valid_wb <= '0;
        order_wb      <= '0;
        instr_wb      <= '0;
        trap_wb       <= '0;
        rs1_addr_wb   <= '0;
        rs2_addr_wb   <= '0;
        rs1_rdata_wb  <= '0;
        rs2_rdata_wb  <= '0;
        pc_wb         <= '0;
        pc_n_wb       <= '0;
        mem_addr_wb   <= '0;
        mem_rmask_wb  <= '0;
        mem_wmask_wb  <= '0;
        // mem_rdata_wb <= '0;
        mem_wdata_wb  <= '0;
        csr_wdata_wb  <= '0;
        csr_rdata_wb  <= '0;
    end else begin
        order_wb <= order_wb + {63'b0, rvfi_valid};
        trap_wb  <= trap_mem;
        pc_wb    <= pc_mem;
        pc_n_wb  <= pc_n_mem;
        if (valid_mem) begin
            rvfi_valid_wb <= rvfi_valid_mem;
            instr_wb      <= instr_mem;
            // trap_wb      <= trap_mem;
            rs1_addr_wb   <= rs1_addr_mem;
            rs2_addr_wb   <= rs2_addr_mem;
            rs1_rdata_wb  <= rs1_rdata_mem;
            rs2_rdata_wb  <= rs2_rdata_mem;
            // pc_wb        <= pc_mem;
            // pc_n_wb      <= pc_n_mem;
            mem_addr_wb   <= dmem_addr_o;
            mem_rmask_wb  <= dmem_ben_o;
            mem_wmask_wb  <= (dmem_wen_o) ? (dmem_ben_o) : ('0);
            // mem_rdata_wb <= '0;
            mem_wdata_wb  <= dmem_wdata_o;
            csr_wdata_wb  <= csr_wdata_mem;
            csr_rdata_wb  <= csr_wdata_mem;
        end
        // Insert bubble if previous stage wasn't valid
        else begin
            rvfi_valid_wb <= '0;
            instr_wb      <= '0;
            // trap_wb      <= '0;
            rs1_addr_wb   <= '0;
            rs2_addr_wb   <= '0;
            rs1_rdata_wb  <= '0;
            rs2_rdata_wb  <= '0;
            // pc_wb        <= '0;
            // pc_n_wb      <= '0;
            mem_addr_wb   <= '0;
            mem_rmask_wb  <= '0;
            mem_wmask_wb  <= '0;
            // mem_rdata_wb <= '0;
            mem_wdata_wb  <= '0;
            csr_wdata_wb  <= '0;
            csr_rdata_wb  <= '0;
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
assign rvfi_intr = 1'b0;
assign rvfi_mode = 2'b11;
assign rvfi_ixl  = 2'b01;

// Integer Register Read/Write
assign rvfi_rs1_addr  = rs1_addr_wb;
assign rvfi_rs1_rdata = rs1_rdata_wb;
assign rvfi_rs2_addr  = rs2_addr_wb;
assign rvfi_rs2_rdata = rs2_rdata_wb;
assign rvfi_rd_addr  = (reg_wen_wb) ? (rd_addr_wb) : ('0);
assign rvfi_rd_wdata = (!rvfi_rd_addr) ? ('0) : (reg_wdata_wb);

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
wire [31:0] csr_mask_wb = {32{rvfi_valid_wb}};
assign rvfi_csr_misa_rmask = '1;
assign rvfi_csr_misa_rdata = misa;
assign rvfi_csr_misa_wmask = csr_mask_wb;
assign rvfi_csr_misa_wdata = csr_wdata_wb;

`define assign_rvfi_csr(name) \
assign rvfi_csr_``name``_rmask = csr_mask_wb; \
assign rvfi_csr_``name``_rdata = csr_rdata_wb; \
assign rvfi_csr_``name``_wmask = csr_mask_wb; \
assign rvfi_csr_``name``_wdata = csr_wdata_wb;

`assign_rvfi_csr(mhartid)
`assign_rvfi_csr(mvendorid)
`assign_rvfi_csr(marchid)
`assign_rvfi_csr(mimpid)

endmodule



                // rs1_addr_ex   <= (alu_source_1_id == ALU_SCR1_RS1) ? (rs1_addr_id) : ('0);
                // rs2_addr_ex   <= (alu_source_2_id == ALU_SCR2_RS2) ? (rs2_addr_id) : ('0);
                // rs1_rdata_ex   <= (alu_source_1_id == ALU_SCR1_RS1) ? (rs1_or_fwd_id) : ('0);
                // rs2_rdata_ex   <= (alu_source_2_id == ALU_SCR2_RS2) ? (rs2_or_fwd_id) : ('0);