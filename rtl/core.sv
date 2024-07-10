/*
    Author: Pedro Medeiros (pedromedeiros.egnr@gmail.com)
    
    This is a very simple pipelined RISC-V core.
    RV32I ISA, in-order, 5 pipeline stages (Instruction Fetch, Instruction Decode, 
    Execution, Memory Access, Write Back).
*/

module core (
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
    output logic [31:0] imem_addr_o

`ifdef RISCV_FORMAL
    ,
    `RVFI_OUTPUTS
`endif
);

import core_pkg::*;

// Program Counter, Instruction and pipeline control signals
logic [31:0] pc_if, pc_if_n, pc_id;
logic [31:0] instr_if, instr_id;
logic        valid_if, valid_id, valid_ex, valid_mem, valid_wb;
// logic        ready_if, ready_id, ready_ex, ready_mem, ready_wb;
logic        stall_if, stall_id;
logic        flush_id, flush_ex;

// Source and destiny registers from register file
logic [ 4:0] rs1_addr_id, rs2_addr_id;
logic [31:0] rs1_rdata_id, rs2_rdata_id;
logic [31:0] rs1_or_fwd_id, rs2_or_fwd_id;
logic [ 4:0] rd_addr_id, rd_addr_ex, rd_addr_mem, rd_addr_wb;

// ALU control signals, operands and result
alu_operation_t    alu_operation_id, alu_operation_ex;
alu_source_1_t     alu_source_1_id; 
alu_source_2_t     alu_source_2_id; 
immediate_source_t immediate_type_id;
logic [31:0]       immediate_id;
logic [31:0]       alu_operand_1_id, alu_operand_1_ex;
logic [31:0]       alu_operand_2_id, alu_operand_2_ex;
logic [31:0]       alu_result_ex, alu_result_mem, alu_result_wb;
forward_t          fwd_op1_id, fwd_op2_id;

// Memory access control signals, write data and read data
logic        mem_wen_id, mem_wen_ex, mem_wen_mem;
data_type_t  mem_data_type_id, mem_data_type_ex, mem_data_type_mem;
logic        mem_sign_extend_id, mem_sign_extend_ex, mem_sign_extend_mem;
logic [31:0] mem_wdata_id, mem_wdata_ex, mem_wdata_mem;
logic [31:0] mem_rdata_mem, mem_rdata_wb;

// Register file write enables and write data (distinguish between writes from ALU or from loads)
logic        reg_alu_wen_id, reg_alu_wen_ex, reg_alu_wen_mem, reg_alu_wen_wb; 
logic        reg_mem_wen_id, reg_mem_wen_ex, reg_mem_wen_mem, reg_mem_wen_wb; 
logic        reg_wen_wb;
logic [31:0] reg_wdata_wb;

// Program Counter control and branch target
pc_source_t  pc_source_id, pc_source_ex; 
logic        is_branch_id, is_branch_ex;
logic [31:0] branch_target_id, branch_target_ex;
logic [31:0] jump_target_id;
logic        branch_decision_ex;

// Indicator of illegal instruction
logic illegal_instr_id;



///////////////////////////////////////////////////////////////////////////////
///////////////////////        INSTRUCTION FETCH        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Instruction Memory Interface
assign instr_if = imem_rdata_i; // Instruction read from memory
assign imem_addr_o = pc_if;     // Address from which the instruction is fetched

// Pipeline registers
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        pc_if <= 0;
    end else begin
        if (!stall_if) begin
            pc_if <= pc_if_n;
        end
    end
end

// Determine next instruction address (PC)
always_comb begin
    if (valid_id && (pc_source_id == PC_JAL || pc_source_id == PC_JALR))
        pc_if_n = jump_target_id;
    else if (pc_source_ex == PC_BRANCH && branch_decision_ex)
        pc_if_n = branch_target_ex;
    else
        pc_if_n = pc_if + 32'd4;
end

// Resolve validness. Not valid implies inserting bubble
assign valid_if = !stall_if && !flush_id;


///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION DECODE        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        pc_id    <= '0;
        instr_id <= '0;
    end else begin
        if (!stall_id) begin
            if (valid_if) begin
                pc_id    <= pc_if;
                instr_id <= instr_if;
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                // instr_id <= '0;
                instr_id <= 32'h0000_0013; // NOP instruction
            end
        end
    end
end

decoder #(
    .ISA_M ( 0 )
) decoder_inst (
    // ALU related signals
	.alu_operation_o  ( alu_operation_id ),
    .alu_source_1_o   ( alu_source_1_id ), 
    .alu_source_2_o   ( alu_source_2_id ), 
    .immediate_type_o ( immediate_type_id ),
    
    // Source/destiny general purpose registers
    .rs1_addr_o (rs1_addr_id),
    .rs2_addr_o (rs2_addr_id),
    .rd_addr_o  (rd_addr_id),
    
    // Memory access related signals
    .mem_wen_o         ( mem_wen_id ),
    .mem_data_type_o   ( mem_data_type_id ),
    .mem_sign_extend_o ( mem_sign_extend_id ),
    
    // Write enable for ALU and mem access operations
    .reg_alu_wen_o ( reg_alu_wen_id ), 
    .reg_mem_wen_o ( reg_mem_wen_id ), 
    
    // Control transfer related signals
    .pc_source_o ( pc_source_id ), 
    .is_branch_o ( is_branch_id ),
    
    // Decoded an illegal instruction
    .illegal_instr_o ( illegal_instr_id ),
    
    // Instruction to be decoded
	.instr_i ( instr_id )
);

imm_extender imm_extender_inst (
    .immediate        ( immediate_id ),
    .immediate_type_i ( immediate_type_id ),
    .instr_i          ( instr_id )
);

register_file register_file_inst (
    .rdata1_o ( rs1_rdata_id ),
    .rdata2_o ( rs2_rdata_id ),
    .raddr1_i ( rs1_addr_id ),
    .raddr2_i ( rs2_addr_id ),
    
    .wdata_i  ( reg_wdata_wb ),
    .waddr_i  ( rd_addr_wb ),
    .wen_i    ( reg_wen_wb ),
    
    .clk_i    ( clk_i ),
    .rst_n_i  ( rst_n_i )
);

// Resolve forwarding for rs1 and rs2
always_comb begin
    unique case (fwd_op1_id)
        NO_FORWARD           : rs1_or_fwd_id = rs1_rdata_id;
        FWD_EX_TO_ID         : rs1_or_fwd_id = alu_result_ex;
        FWD_MEM_ALU_RES_TO_ID: rs1_or_fwd_id = alu_result_mem;
        FWD_MEM_RDATA_TO_ID  : rs1_or_fwd_id = mem_rdata_mem;
        FWD_WB_ALU_RES_TO_ID : rs1_or_fwd_id = alu_result_wb;
        FWD_WB_RDATA_TO_ID   : rs1_or_fwd_id = mem_rdata_wb;
        default: rs1_or_fwd_id = rs1_rdata_id;
    endcase
    unique case (fwd_op2_id)
        NO_FORWARD           : rs2_or_fwd_id = rs2_rdata_id;
        FWD_EX_TO_ID         : rs2_or_fwd_id = alu_result_ex;
        FWD_MEM_ALU_RES_TO_ID: rs2_or_fwd_id = alu_result_mem;
        FWD_MEM_RDATA_TO_ID  : rs2_or_fwd_id = mem_rdata_mem;
        FWD_WB_ALU_RES_TO_ID : rs2_or_fwd_id = alu_result_wb;
        FWD_WB_RDATA_TO_ID   : rs2_or_fwd_id = mem_rdata_wb;
        default: rs2_or_fwd_id = rs2_rdata_id;
    endcase
end

// ALU operands
always_comb begin
    unique case (alu_source_1_id)
        ALU_SCR1_RS1 : alu_operand_1_id = rs1_or_fwd_id;
        ALU_SCR1_PC  : alu_operand_1_id = pc_id;
        ALU_SCR1_ZERO: alu_operand_1_id = 32'b0;
        default: alu_operand_1_id = 32'b0;
    endcase
    unique case (alu_source_2_id)
        ALU_SCR2_RS2   : alu_operand_2_id = rs2_or_fwd_id;
        ALU_SCR2_IMM   : alu_operand_2_id = immediate_id;
        ALU_SCR2_4_OR_2: alu_operand_2_id = 32'd4;
        default: alu_operand_1_id = 32'b0;
    endcase
end

// Pass forward the data to write in the memory
assign mem_wdata_id = rs2_or_fwd_id;

// Calculate branch target
assign branch_target_id = pc_id + immediate_id;

// Calculate jump target
always_comb begin
    unique case (pc_source_id)
        PC_JAL : jump_target_id = pc_id + immediate_id;
        PC_JALR: jump_target_id = rs1_or_fwd_id + immediate_id;
        default: jump_target_id = pc_id + immediate_id;
    endcase
end

// Resolve validness. Not valid implies inserting bubble
assign valid_id = !stall_id && !flush_ex && !illegal_instr_id;

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_ex         <= '0;
        alu_operation_ex   <= ALU_ADD;
        alu_operand_1_ex   <= '0;
        alu_operand_2_ex   <= '0;
        mem_wen_ex         <= '0;
        mem_data_type_ex   <= WORD;
        mem_sign_extend_ex <= '0;
        mem_wdata_ex       <= '0;
        reg_alu_wen_ex     <= '0;
        reg_mem_wen_ex     <= '0;
        pc_source_ex       <= PC_P_4;
        is_branch_ex       <= '0;
        branch_target_ex   <= '0;
    end else begin
        if (valid_id) begin
            rd_addr_ex         <= rd_addr_id;
            alu_operation_ex   <= alu_operation_id;
            alu_operand_1_ex   <= alu_operand_1_id;
            alu_operand_2_ex   <= alu_operand_2_id;
            mem_wen_ex         <= mem_wen_id;
            mem_data_type_ex   <= mem_data_type_id;
            mem_sign_extend_ex <= mem_sign_extend_id;
            mem_wdata_ex       <= mem_wdata_id;
            reg_alu_wen_ex     <= reg_alu_wen_id;
            reg_mem_wen_ex     <= reg_mem_wen_id;
            pc_source_ex       <= pc_source_id;
            is_branch_ex       <= is_branch_id;
            branch_target_ex   <= branch_target_id;
        end
        // Insert bubble if previous stage wasn't valid
        else begin
            mem_wen_ex         <= '0;
            reg_alu_wen_ex     <= '0;
            reg_mem_wen_ex     <= '0;
            is_branch_ex       <= '0;
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

// Control signal for branches (this will invalidate IF and ID)
assign branch_decision_ex = is_branch_ex && alu_result_ex[0];



///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_mem         <= '0;
        alu_result_mem      <= '0;
        mem_wen_mem         <= '0;
        mem_data_type_mem   <= WORD;
        mem_sign_extend_mem <= '0;
        mem_wdata_mem       <= '0;
        reg_alu_wen_mem     <= '0;
        reg_mem_wen_mem     <= '0;
    end else begin
        rd_addr_mem         <= rd_addr_ex;
        alu_result_mem      <= alu_result_ex;
        mem_wen_mem         <= mem_wen_ex;
        mem_data_type_mem   <= mem_data_type_ex;
        mem_sign_extend_mem <= mem_sign_extend_ex;
        mem_wdata_mem       <= mem_wdata_ex;
        reg_alu_wen_mem     <= reg_alu_wen_ex;
        reg_mem_wen_mem     <= reg_mem_wen_ex;
    end
end

// Data Memory Interface
assign dmem_wdata_o = mem_wdata_mem;
assign dmem_addr_o  = alu_result_mem;
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
                mem_rdata_mem = {{24{dmem_rdata_i[7]}}, dmem_rdata_i[7:0]};
            else
                mem_rdata_mem = {24'b0, dmem_rdata_i[7:0]};
        end
        HALF_WORD: begin
            if (mem_sign_extend_mem)
                mem_rdata_mem = {{16{dmem_rdata_i[15]}}, dmem_rdata_i[15:0]};
            else
                mem_rdata_mem = {16'b0, dmem_rdata_i[15:0]};
        end
        WORD     : begin
            mem_rdata_mem = dmem_rdata_i;
        end
        default: mem_rdata_mem = dmem_rdata_i;
    endcase
end



///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

// Pipeline registers
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_wb         <= '0;
        alu_result_wb      <= '0;
        // mem_data_type_wb   <= '0;
        // mem_sign_extend_wb <= '0;
        mem_rdata_wb       <= '0;
        reg_alu_wen_wb     <= '0;
        reg_mem_wen_wb     <= '0;
    end else begin
        rd_addr_wb         <= rd_addr_mem;
        alu_result_wb      <= alu_result_mem;
        // mem_data_type_wb   <= mem_data_type_mem;
        // mem_sign_extend_wb <= mem_sign_extend_mem;
        // mem_rdata_wb       <= dmem_rdata_i;
        mem_rdata_wb       <= mem_rdata_mem;
        reg_alu_wen_wb     <= reg_alu_wen_mem;
        reg_mem_wen_wb     <= reg_mem_wen_mem;
    end
end

// always_comb begin
//     unique case (mem_data_type_wb)
//         BYTE     : begin
//             if (mem_sign_extend_wb)
//                 mem_rdata_ext_wb = {24{mem_rdata_wb[7]}, mem_rdata_wb[7:0]};
//             else
//                 mem_rdata_ext_wb = {24'b0, mem_rdata_wb[7:0]};
//         end
//         HALF_WORD: begin
//             if (mem_sign_extend_wb)
//                 mem_rdata_ext_wb = {16{mem_rdata_wb[15]}, mem_rdata_wb[15:0]};
//             else
//                 mem_rdata_ext_wb = {16'b0, mem_rdata_wb[15:0]};
//         end
//         WORD     : begin
//             mem_rdata_ext_wb = mem_rdata_wb;
//         end
//         default: mem_rdata_ext_wb = mem_rdata_wb;
//     endcase
// end

// Determine write enable and write data for the register file
always_comb begin
    if (reg_alu_wen_wb)
        reg_wdata_wb = alu_result_wb;
    else if (reg_mem_wen_wb)
        // reg_wdata_wb = mem_rdata_ext_wb;
        reg_wdata_wb = mem_rdata_wb;
    else
        // reg_wdata_wb = '0;
        reg_wdata_wb = alu_result_wb;
    
    reg_wen_wb = reg_alu_wen_wb || reg_mem_wen_wb;
end



///////////////////////////////////////////////////////////////////////////////
////////////////////////          CONTROLLER          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

controller controller_inst (
    // Data Hazards (forwarding)
    .fwd_op1_o ( fwd_op1_id ),
    .fwd_op2_o ( fwd_op2_id ),
    
    // Source/destiny general purpose registers
    .rs1_addr_id_i     ( rs1_addr_id ),
    .rs2_addr_id_i     ( rs2_addr_id ),
    .rd_addr_ex_i      ( rd_addr_ex ),
    .rd_addr_mem_i     ( rd_addr_mem ),
    .rd_addr_wb_i      ( rd_addr_wb ),
    // Write enables
    .reg_alu_wen_ex_i  ( reg_alu_wen_ex ),
    .reg_alu_wen_mem_i ( reg_alu_wen_mem ),
    .reg_alu_wen_wb_i  ( reg_alu_wen_wb ),
    .reg_mem_wen_mem_i ( reg_mem_wen_mem ),
    .reg_mem_wen_wb_i  ( reg_mem_wen_wb ),
    
    // Data Hazards (stalling)
    .stall_if_o ( stall_if ),
    .stall_id_o ( stall_id ),
    
    .reg_mem_wen_ex_i ( reg_mem_wen_ex ),
    
    // Control Hazards (flushing)
    .flush_id_o ( flush_id ),
    .flush_ex_o ( flush_ex ),
    
    .pc_source_id_i       ( pc_source_id ),
    .branch_decision_ex_i ( branch_decision_ex )
);

endmodule