module pc_controller import core_pkg::*; #(
    parameter int WIDTH = 32
) (
    output logic [WIDTH-1:0] next_pc_o,
    input  logic [WIDTH-1:0] curr_pc_i, 
    input  logic             valid_id_i,
    input  logic [WIDTH-1:0] jump_target_id_i, 
    input  logic [WIDTH-1:0] branch_target_ex_i, 
    input  logic             branch_decision_ex_i,
    input  logic             is_compressed_if_o,
    input  pc_source_t       pc_source_id_i,
    input  pc_source_t       pc_source_ex_i
);

// Determine next instruction address (PC)
always_comb begin
    if (valid_id_i && (pc_source_id_i == PC_JAL || pc_source_id_i == PC_JALR))
        next_pc_o = jump_target_id_i;
    else if (pc_source_ex_i == PC_BRANCH && branch_decision_ex_i)
        next_pc_o = branch_target_ex_i;
    else if (is_compressed_if_o)
        next_pc_o = curr_pc_i + 32'd2;
    else
        next_pc_o = curr_pc_i + 32'd4;
end

endmodule