module pc_controller import core_pkg::*; #(
    parameter int WIDTH = 32
) (
    // output logic [WIDTH-1:0] next_pc_o,
    // input  logic [WIDTH-1:0] curr_pc_i, 
    // input  logic [WIDTH-1:0] ctrl_transfer_target_i, 
    // input  pc_source_t       pc_src_i,
    // input  logic [WIDTH-1:0] imm_i,
    // input  logic             branch_decision_i
);

// Determine next instruction address (PC)
always_comb begin
    if (valid_id && (pc_source_id == PC_JAL || pc_source_id == PC_JALR))
        pc_if_n = jump_target_id;
    else if (pc_source_ex == PC_BRANCH && branch_decision_ex)
        pc_if_n = branch_target_ex;
    else
        pc_if_n = pc_if + 32'd4;
end

endmodule