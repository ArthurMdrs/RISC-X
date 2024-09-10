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

module register_file #(
    parameter int AWIDTH = 5,
    parameter int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] rdata1_o,
    output logic [DWIDTH-1:0] rdata2_o,
    input  logic [AWIDTH-1:0] raddr1_i,
    input  logic [AWIDTH-1:0] raddr2_i,
    input  logic [DWIDTH-1:0] wdata_i,
    input  logic [AWIDTH-1:0] waddr_i,
    input  logic              wen_i,
    input  logic              clk_i,
    input  logic              rst_n_i
);

localparam MEM_SIZE = 2**AWIDTH;

// Internal memory
logic [DWIDTH-1:0] mem [1:MEM_SIZE-1];

// Define write operation
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // mem <= '{(MEM_SIZE){'0}};
        for (int i = 1; i < MEM_SIZE; i++)
            mem[i] <= '0;
    end else begin
        if (wen_i && waddr_i != 0)
            mem[waddr_i] <= wdata_i;
    end
end

// Define read operation
always_comb begin
    rdata1_o = (!raddr1_i) ? ('0) : (mem[raddr1_i]);
    rdata2_o = (!raddr2_i) ? ('0) : (mem[raddr2_i]);
end
    
endmodule