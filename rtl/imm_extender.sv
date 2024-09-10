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
//                 Túlio Tavares -                                            //
//                 Victor Melquíades -                                        //
//                                                                            //
// Design Name:    Immediate extender                                         //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decodes the immediate operand from the instruction bits    //
//                 and zero/sign extends it.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

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
        IMM_B: immediate = {{(DWIDTH-13){instr_i[31]}}, instr_i[31], instr_i[7], instr_i[30:25], instr_i[11:8], 1'b0};
        IMM_U: immediate = {{(DWIDTH-32){instr_i[31]}}, instr_i[31:12], 12'b0};
        IMM_J: immediate = {{(DWIDTH-21){instr_i[31]}}, instr_i[31], instr_i[19:12], instr_i[20], instr_i[30:21], 1'b0};
      

        IMM_CJ:   immediate = {{(DWIDTH-12){instr_i[12]}}, instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], 1'b0};    // J/JAL
        IMM_CJR:  immediate = 32'b0;                                                                                                                                        // JR/JALR
        IMM_CI:   immediate = {{(DWIDTH-6){instr_i[12]}}, instr_i[12], instr_i[6:2]};                                                                                       // LI/ADDi/SLLi/SRLi/SRAi/ANDi
        IMM_CIW:  immediate = {{(DWIDTH-10){1'b0}}, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b0};                                                           // ADDI4SPN
        IMM_CLUI: immediate = {{(DWIDTH-18){instr_i[12]}}, instr_i[12], instr_i[6:2], 12'b0};                                                                               // LUI
        IMM_CSPL: immediate = {{(DWIDTH-8){1'b0}}, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b0};                                                                          // LWSP/FLWSP (32 bit)
        IMM_CSPS: immediate = {{(DWIDTH-8){1'b0}}, instr_i[8:7], instr_i[12:9], 2'b0};                                                                                      // SWSP/FSWSP (32 bit)
        IMM_CLS:  immediate = {{(DWIDTH-7){1'b0}}, instr_i[5], instr_i[12:10], instr_i[6], 2'b0};                                                                           // LW/FLW/SW/FSW (32 bit)
        IMM_CB:   immediate = {{(DWIDTH-9){instr_i[12]}}, instr_i[12], instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3], 1'b0};                                       // BEQ/BNE
        IMM_C16:  immediate = {{(DWIDTH-10){instr_i[12]}}, instr_i[12], instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 4'b0};                                            // ADDi16SP

        default: immediate = {{(DWIDTH-12){instr_i[31]}}, instr_i[31:20]};
    endcase
end

endmodule
