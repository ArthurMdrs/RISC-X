// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    Basic ALU                                                  //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Arithmetic and Logic Unit with basic functions, enough to  //
//                 run the RV32I set.                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module alu import core_pkg::*; #(
    parameter int DWIDTH = 8
) (
    output logic [DWIDTH-1:0] res_o,
    input  logic [DWIDTH-1:0] op1_i,
    input  logic [DWIDTH-1:0] op2_i,
    input  alu_operation_t    operation_i
);

logic signed [DWIDTH-1:0] op1_s, op2_s;

`ifdef JASPER
`default_nettype none
`endif

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

`ifdef JASPER
`default_nettype wire
`endif

endmodule