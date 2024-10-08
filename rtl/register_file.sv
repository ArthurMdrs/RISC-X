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
// Design Name:    Register file                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Contains the core's general purpose registers (GPRs).      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module register_file import core_pkg::*; #(
    parameter int AWIDTH = 5,
    parameter int DWIDTH = 32,
    parameter bit GEN_F_REGS = 0
) (
    input  logic              clk_i,
    input  logic              rst_n_i,
    
    input  logic [DWIDTH-1:0] wdata_i,
    input  logic [AWIDTH-1:0] waddr_i,
    input  logic              wen_i,
    input  reg_bank_mux_t     wdst_i,
    
    output logic [DWIDTH-1:0] rdata1_o,
    output logic [DWIDTH-1:0] rdata2_o,
    output logic [DWIDTH-1:0] rdata3_o,
    input  logic [AWIDTH-1:0] raddr1_i,
    input  logic [AWIDTH-1:0] raddr2_i,
    input  logic [AWIDTH-1:0] raddr3_i,
    
    input  reg_bank_mux_t rsrc1_i,
    input  reg_bank_mux_t rsrc2_i,
    input  reg_bank_mux_t rsrc3_i
);

// localparam MEM_SIZE = (2**AWIDTH) * (1 + GEN_F_REGS);
localparam MEM_SIZE = 2**AWIDTH;

// Integer registers
logic [DWIDTH-1:0] mem_x [1:MEM_SIZE-1];
// Floating-point registers
logic [DWIDTH-1:0] mem_f [0:MEM_SIZE-1];

`ifdef JASPER
`default_nettype none
`endif

// Define write operation
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // mem_x <= '{(MEM_SIZE){'0}};
        for (int i = 1; i < MEM_SIZE; i++)
            mem_x[i] <= '0;
    end else begin
        if (wen_i && waddr_i != 0 && wdst_i == X_REG)
            mem_x[waddr_i] <= wdata_i;
    end
end

generate
    if (GEN_F_REGS) begin : gen_f_regs
        // Define write operation
        always_ff @(posedge clk_i, negedge rst_n_i) begin
            if (!rst_n_i) begin
                // mem_f <= '{(MEM_SIZE){'0}};
                for (int i = 0; i < MEM_SIZE; i++)
                    mem_f[i] <= '0;
            end else begin
                if (wen_i && wdst_i == F_REG)
                    mem_f[waddr_i] <= wdata_i;
            end
        end
    end : gen_f_regs
    else begin : no_gen_f_regs
        always_comb begin
            for (int i = 1; i < MEM_SIZE; i++)
                mem_f[i] = '0;
        end
    end : no_gen_f_regs
endgenerate
        

// Define read operation
// always_comb begin
//     if (raddr1_i == '0) begin
//         rdata1_o = '0;
//     end else if (!GEN_F_REGS) begin
//         rdata1_o = mem_x[raddr1_i];
//     end else begin
//         unique case (rsrc1_i)
//             X_REG: rdata1_o = mem_x[raddr1_i];
//             F_REG: rdata1_o = mem_f[raddr1_i];
//             default: rdata1_o = '0;
//         endcase
//     end
    
//     if (raddr2_i == '0) begin
//         rdata2_o = '0;
//     end else if (!GEN_F_REGS) begin
//         rdata2_o = mem_x[raddr2_i];
//     end else begin
//         unique case (rsrc2_i)
//             X_REG: rdata2_o = mem_x[raddr2_i];
//             F_REG: rdata2_o = mem_f[raddr2_i];
//             default: rdata2_o = '0;
//         endcase
//     end
    
//     if (raddr3_i == '0) begin
//         rdata3_o = '0;
//     end else if (!GEN_F_REGS) begin
//         rdata3_o = mem_x[raddr3_i];
//     end else begin
//         unique case (rsrc3_i)
//             X_REG: rdata3_o = mem_x[raddr3_i];
//             F_REG: rdata3_o = mem_f[raddr3_i];
//             default: rdata3_o = '0;
//         endcase
//     end
    
//     // rdata1_o = (!raddr1_i) ? ('0) : (mem_x[raddr1_i]);
//     // rdata2_o = (!raddr2_i) ? ('0) : (mem_x[raddr2_i]);
// end
// Define read operation
always_comb begin
    if (!GEN_F_REGS) begin
        if (raddr1_i == '0) rdata1_o = '0;
        else                rdata1_o = mem_x[raddr1_i];
    end else begin
        unique case (rsrc1_i)
            X_REG: begin
                if (raddr1_i == '0) rdata1_o = '0;
                else                rdata1_o = mem_x[raddr1_i];
            end
            F_REG: begin
                rdata1_o = mem_f[raddr1_i];
            end
            default: rdata1_o = '0;
        endcase
    end
    
    if (!GEN_F_REGS) begin
        if (raddr2_i == '0) rdata2_o = '0;
        else                rdata2_o = mem_x[raddr2_i];
    end else begin
        unique case (rsrc2_i)
            X_REG: begin
                if (raddr2_i == '0) rdata2_o = '0;
                else                rdata2_o = mem_x[raddr2_i];
            end
            F_REG: begin
                rdata2_o = mem_f[raddr2_i];
            end
            default: rdata2_o = '0;
        endcase
    end
    
    if (!GEN_F_REGS) begin
        if (raddr3_i == '0) rdata3_o = '0;
        else                rdata3_o = mem_x[raddr3_i];
    end else begin
        unique case (rsrc3_i)
            X_REG: begin
                if (raddr3_i == '0) rdata3_o = '0;
                else                rdata3_o = mem_x[raddr3_i];
            end
            F_REG: begin
                rdata3_o = mem_f[raddr3_i];
            end
            default: rdata3_o = '0;
        endcase
    end
end

`ifdef JASPER
`default_nettype wire
`endif
    
endmodule