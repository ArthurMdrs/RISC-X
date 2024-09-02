module if_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic [29:0] boot_addr_i,
    
    // Interface with instruction memory
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o,
    
    // Output to ID stage
    output logic [31:0] pc_if_o,
    output logic [31:0] instr_if_o,
    output logic        valid_if_o,
    output logic        is_compressed_if_o,
    
    // Control inputs
    input  logic stall_if_i,
    
    // Trap handling
    input               trap_id_i,
    input               trap_ex_i,
    input               is_mret_i,
    input  logic [31:0] mtvec_i,
    input  logic [31:0] mepc_i,
    
    // Signals for the PC controller
    input  logic        valid_id_i,
    input  logic        valid_ex_i,
    input  logic [31:0] jump_target_id_i, 
    input  logic [31:0] branch_target_ex_i, 
    input  logic        branch_decision_ex_i,
    input  pc_source_t  pc_source_id_i,
    input  pc_source_t  pc_source_ex_i
);

///////////////////////////////////////////////////////////////////////////////
///////////////////////        INSTRUCTION FETCH        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic [31:0] pc_if_n;
// logic        is_compressed_if_o;

`default_nettype none

// Next instruction pointer decision maker
assign is_compressed_if_o = ~(imem_rdata_i[1] && imem_rdata_i[0]);
    
// Instruction Memory Interface
assign instr_if_o = imem_rdata_i; // Instruction read from memory
assign imem_addr_o = pc_if_o;     // Address from which the instruction is fetched

// Pipeline registers ->IF
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        pc_if_o <= {boot_addr_i, 2'b0};
    end else begin
        if (!stall_if_i) begin
            pc_if_o <= pc_if_n;
        end
    end
end

// Determine next instruction address (PC)
pc_controller pc_constroller_inst (
    .next_pc_o            ( pc_if_n ),
    .curr_pc_i            ( pc_if_o ), 
    .valid_id_i           ( valid_id_i ),
    .jump_target_id_i     ( jump_target_id_i ), 
    .branch_target_ex_i   ( branch_target_ex_i ), 
    .branch_decision_ex_i ( branch_decision_ex_i ),
    .is_compressed_if_i   ( is_compressed_if_o),
    .pc_source_id_i       ( pc_source_id_i ),
    .pc_source_ex_i       ( pc_source_ex_i ),
    .trap_id_i            ( trap_id_i ),
    .trap_ex_i            ( trap_ex_i ),
    
    .is_mret_i            ( is_mret_i ),
    .mtvec_i              ( mtvec_i ),
    .mepc_i               ( mepc_i )
);

// Resolve validness. Not valid implies inserting bubble
assign valid_if_o = 1'b1;

`default_nettype wire

endmodule