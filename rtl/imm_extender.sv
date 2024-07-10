module imm_extender import core_pkg::*; #(
    parameter int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] immediate,
    input  immediate_source_t immediate_type_i,
    input  logic [31:0]       instr_i
);

`ifdef SVA_ON
AST_DWIDTH_MORE_THAN_IMM_SIZE: assert property (@ (instr_i) DWIDTH >= 12);
`endif

always_comb begin
    unique case (immediate_type_i)
        IMM_I: immediate = {{(DWIDTH-12){instr_i[31]}}, instr_i[31:20]};
        IMM_S: immediate = {{(DWIDTH-12){instr_i[31]}}, instr_i[31:25], instr_i[11:7]};
        IMM_B: immediate = {{(DWIDTH-11){instr_i[31]}}, instr_i[31], instr_i[7], instr_i[30:25], instr_i[11:8], 1'b0};
        IMM_U: immediate = {{(DWIDTH-32){instr_i[31]}}, instr_i[31:12], 12'b0};
        IMM_J: immediate = {{(DWIDTH-11){instr_i[31]}}, instr_i[31], instr_i[19:12], instr_i[20], instr_i[30:21], 1'b0};
        default: immediate = {{(DWIDTH-12){instr_i[31]}}, instr_i[31:20]};
    endcase
end

endmodule