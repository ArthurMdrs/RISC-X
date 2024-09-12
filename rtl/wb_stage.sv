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
// Design Name:    Writeback stage                                            //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Performs writes to the register file.                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module wb_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Input from MEM stage
    input  logic [ 4:0]   rd_addr_mem_i,
    input  reg_bank_mux_t rd_dst_bank_mem_i,
    input  logic [31:0]   alu_result_mem_i,
    input  logic [31:0]   mem_rdata_mem_i,
    input  logic          reg_alu_wen_mem_i,
    input  logic          reg_mem_wen_mem_i,
    input  logic          valid_mem_i,
    
    // Output to register file
    output logic [31:0] reg_wdata_wb_o,
    output logic        reg_wen_wb_o,
    
    // Output for forwarding
    output logic [ 4:0]   rd_addr_wb_o,
    output reg_bank_mux_t rd_dst_bank_wb_o,
    output logic [31:0]   alu_result_wb_o,
    output logic [31:0]   mem_rdata_wb_o,
    output logic          reg_alu_wen_wb_o,
    output logic          reg_mem_wen_wb_o,
    
    // Control inputs
    input  logic flush_wb_i
);

///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

`ifdef JASPER
`default_nettype none
`endif

// Pipeline registers MEM->WB
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_wb_o     <= '0;
        rd_dst_bank_wb_o <= X_REG;
        alu_result_wb_o  <= '0;
        mem_rdata_wb_o   <= '0;
        reg_alu_wen_wb_o <= '0;
        reg_mem_wen_wb_o <= '0;
    end else begin
        // Insert bubble if flushing is needed
        if (flush_wb_i) begin
            reg_alu_wen_wb_o <= '0;
            reg_mem_wen_wb_o <= '0;
        end
        else begin
            rd_addr_wb_o     <= rd_addr_mem_i;
            rd_dst_bank_wb_o <= rd_dst_bank_mem_i;
            alu_result_wb_o  <= alu_result_mem_i;
            mem_rdata_wb_o   <= mem_rdata_mem_i;
            reg_alu_wen_wb_o <= reg_alu_wen_mem_i;
            reg_mem_wen_wb_o <= reg_mem_wen_mem_i;
        end
    end
end

// Determine write enable and write data for the register file
always_comb begin
    if (reg_alu_wen_wb_o)
        reg_wdata_wb_o = alu_result_wb_o;
    else if (reg_mem_wen_wb_o)
        reg_wdata_wb_o = mem_rdata_wb_o;
    else
        reg_wdata_wb_o = alu_result_wb_o;
    
    reg_wen_wb_o = reg_alu_wen_wb_o || reg_mem_wen_wb_o;
end

`ifdef JASPER
`default_nettype wire
`endif

endmodule
