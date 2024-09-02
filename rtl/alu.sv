module alu import core_pkg::*; #(
    parameter int DWIDTH = 8
) (
    output logic [DWIDTH-1:0] res_o,
    input  logic [DWIDTH-1:0] op1_i,
    input  logic [DWIDTH-1:0] op2_i,
    input  alu_operation_t    operation_i
);

logic signed [DWIDTH-1:0] op1_s, op2_s;

`default_nettype none

assign op1_s = op1_i;
assign op2_s = op2_i;

always_comb
    case (operation_i)
        ALU_AND : res_o = op1_i & op2_i;
        ALU_OR  : res_o = op1_i | op2_i;
        ALU_XOR : res_o = op1_i ^ op2_i;
        
        ALU_ADD : res_o = op1_i + op2_i;
        ALU_SUB : res_o = op1_i - op2_i;
        
        ALU_SLL : res_o = op1_i <<  op2_i[4:0];
        ALU_SRL : res_o = op1_i >>  op2_i[4:0];
        ALU_SRA : res_o = op1_s >>> op2_i[4:0];
        
        ALU_SLT : res_o = (op1_s <  op2_s);
        ALU_SLTU: res_o = (op1_i <  op2_i);
        ALU_SGE : res_o = (op1_s >= op2_s);
        ALU_SGEU: res_o = (op1_i >= op2_i);
        ALU_SEQ : res_o = (op1_i == op2_i);
        ALU_SNE : res_o = (op1_i != op2_i);
        default: res_o = 'x;
    endcase

`default_nettype wire

endmodule