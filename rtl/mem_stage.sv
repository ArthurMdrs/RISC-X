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
// Design Name:    Memory stage                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Performs loads and stores from/to memory.                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module mem_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,

    // Interface with data memory
    // input  logic [31:0] dmem_rdata_i,
    // output logic [31:0] dmem_wdata_o,
    // output logic [31:0] dmem_addr_o,
    // output logic        dmem_wen_o,
    // output logic  [3:0] dmem_ben_o,
    
    // OBI interface for data memory
    output logic        data_obi_req_o,
    input  logic        data_obi_gnt_i,
    output logic [31:0] data_obi_addr_o,
    output logic        data_obi_we_o,
    output logic [ 3:0] data_obi_be_o,
    output logic [31:0] data_obi_wdata_o,
    input  logic        data_obi_rvalid_i,
    output logic        data_obi_rready_o,
    input  logic [31:0] data_obi_rdata_i,
    
    // Input from EX stage
    input  logic [ 4:0]   rd_addr_ex_i,
    input  reg_bank_mux_t rd_dst_bank_ex_i,
    input  logic [31:0]   alu_result_ex_i,
    input  logic          mem_req_ex_i,
    input  logic          mem_wen_ex_i,
    input  data_type_t    mem_data_type_ex_i,
    input  logic          mem_sign_extend_ex_i,
    input  logic [31:0]   mem_wdata_ex_i,
    input  logic          reg_alu_wen_ex_i,
    input  logic          reg_mem_wen_ex_i,
    input  logic          valid_ex_i,
    
    // Output to WB stage
    output logic [ 4:0]   rd_addr_mem_o,
    output reg_bank_mux_t rd_dst_bank_mem_o,
    output logic [31:0]   alu_result_mem_o,
    output logic [31:0]   mem_rdata_mem_o,
    output logic          reg_alu_wen_mem_o,
    output logic          reg_mem_wen_mem_o,
    output logic          valid_mem_o,
    
    // Output to controller
    output logic data_obi_busy_mem_o,
    
    // Control inputs
    input  logic stall_mem_i,
    input  logic flush_mem_i
);

///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic        valid_mem_int;

logic        mem_req_mem;
logic        mem_rvalid_mem;
logic        mem_wen_mem;
logic  [3:0] mem_ben_mem;
data_type_t  mem_data_type_mem;
logic        mem_sign_extend_mem;
logic [31:0] mem_addr_mem;
logic [31:0] mem_wdata_mem;
logic [31:0] mem_rdata_int;

logic        obi_tr_cnt;
logic        obi_req;
logic        waiting_obi_gnt, waiting_obi_rvalid;

`ifdef JASPER
`default_nettype none
`endif

// Pipeline registers EX->MEM
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_mem_o         <= '0;
        rd_dst_bank_mem_o     <= X_REG;
        alu_result_mem_o      <= '0;
        mem_req_mem           <= '0;
        mem_wen_mem           <= '0;
        mem_data_type_mem     <= WORD;
        mem_sign_extend_mem   <= '0;
        mem_wdata_mem         <= '0;
        reg_alu_wen_mem_o     <= '0;
        reg_mem_wen_mem_o     <= '0;
        valid_mem_o           <= '0;
        // valid_mem_int         <= '0;
    end else begin
        if (!stall_mem_i) begin
            // Insert bubble if flushing is needed
            if (flush_mem_i) begin
                mem_req_mem           <= '0;
                mem_wen_mem           <= '0;
                reg_alu_wen_mem_o     <= '0;
                reg_mem_wen_mem_o     <= '0;
                valid_mem_o           <= 1'b0;
                // valid_mem_int         <= 1'b0;
            end
            else begin
                rd_addr_mem_o         <= rd_addr_ex_i;
                rd_dst_bank_mem_o     <= rd_dst_bank_ex_i;
                alu_result_mem_o      <= alu_result_ex_i;
                mem_req_mem           <= mem_req_ex_i;
                mem_wen_mem           <= mem_wen_ex_i;
                mem_data_type_mem     <= mem_data_type_ex_i;
                mem_sign_extend_mem   <= mem_sign_extend_ex_i;
                mem_wdata_mem         <= mem_wdata_ex_i;
                reg_alu_wen_mem_o     <= reg_alu_wen_ex_i;
                reg_mem_wen_mem_o     <= reg_mem_wen_ex_i;
                valid_mem_o           <= valid_ex_i;
                // valid_mem_int         <= valid_ex_i;
            end
        end
    end
end

// Data Memory Interface
// assign dmem_wdata_o = mem_wdata_mem;
// assign dmem_addr_o  = alu_result_mem_o;
// assign dmem_wen_o   = mem_wen_mem;

// always_comb begin
//     unique case (mem_data_type_mem)
//         BYTE     : dmem_ben_o = 4'b0001;
//         HALF_WORD: dmem_ben_o = 4'b0011;
//         WORD     : dmem_ben_o = 4'b1111;
//         default: dmem_ben_o = 4'b0000;
//     endcase
// end

// Sign extend the data read from memory
// always_comb begin
//     unique case (mem_data_type_mem)
//         BYTE     : begin
//             if (mem_sign_extend_mem)
//                 mem_rdata_mem_o = {{24{dmem_rdata_i[7]}}, dmem_rdata_i[7:0]};
//             else
//                 mem_rdata_mem_o = {24'b0, dmem_rdata_i[7:0]};
//         end
//         HALF_WORD: begin
//             if (mem_sign_extend_mem)
//                 mem_rdata_mem_o = {{16{dmem_rdata_i[15]}}, dmem_rdata_i[15:0]};
//             else
//                 mem_rdata_mem_o = {16'b0, dmem_rdata_i[15:0]};
//         end
//         WORD     : begin
//             mem_rdata_mem_o = dmem_rdata_i;
//         end
//         default: mem_rdata_mem_o = dmem_rdata_i;
//     endcase
// end


assign mem_addr_mem = alu_result_mem_o;

// Drive byte enable
always_comb begin
    unique case (mem_data_type_mem)
        BYTE     : mem_ben_mem = 4'b0001;
        HALF_WORD: mem_ben_mem = 4'b0011;
        WORD     : mem_ben_mem = 4'b1111;
        default: mem_ben_mem = 4'b0000;
    endcase
end

// Count transactions (max 1 outstanding)
wire obi_tr_cnt_up = data_obi_req_o    && data_obi_gnt_i   ;
wire obi_tr_cnt_dn = data_obi_rvalid_i && data_obi_rready_o;
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        obi_tr_cnt <= 1'b0;
    end else begin
        unique case ({obi_tr_cnt_up, obi_tr_cnt_dn})
            2'b00: obi_tr_cnt <= obi_tr_cnt;        // No  new input tr, no output done
            2'b01: obi_tr_cnt <= (obi_tr_cnt == '0) ? (obi_tr_cnt) : (obi_tr_cnt - 1);    // No  new input tr,    output done
            2'b10: obi_tr_cnt <= obi_tr_cnt + 1;    // Got new input tr, no output done
            2'b11: obi_tr_cnt <= obi_tr_cnt;        // Got new input tr,    output done
            default: obi_tr_cnt <= '0;
        endcase
    end
end

// Assign request for OBI interface
assign obi_req = mem_req_mem && (obi_tr_cnt == '0);

// Assign control signals, used in stalls
assign waiting_obi_gnt = data_obi_req_o && !data_obi_gnt_i;
assign waiting_obi_rvalid = (obi_tr_cnt != '0) && !data_obi_rvalid_i;
// assign data_obi_busy_mem_o = waiting_obi_gnt || waiting_obi_rvalid;

always_comb begin
    // valid_mem_o = valid_mem_int;
    // if (obi_req)
    //     valid_mem_o = 1'b0;
    // if (obi_tr_cnt != '0)
    //     valid_mem_o = data_obi_rvalid_i;
    
    data_obi_busy_mem_o = 1'b0;
    if (obi_req)
        data_obi_busy_mem_o = 1'b1;
    if (obi_tr_cnt != '0)
        data_obi_busy_mem_o = !data_obi_rvalid_i;
end

// Sign extend the data read from memory
always_comb begin
    unique case (mem_data_type_mem)
        BYTE     : begin
            if (mem_sign_extend_mem)
                mem_rdata_mem_o = {{24{mem_rdata_int[7]}}, mem_rdata_int[7:0]};
            else
                mem_rdata_mem_o = {24'b0, mem_rdata_int[7:0]};
        end
        HALF_WORD: begin
            if (mem_sign_extend_mem)
                mem_rdata_mem_o = {{16{mem_rdata_int[15]}}, mem_rdata_int[15:0]};
            else
                mem_rdata_mem_o = {16'b0, mem_rdata_int[15:0]};
        end
        WORD     : begin
            mem_rdata_mem_o = mem_rdata_int;
        end
        default: mem_rdata_mem_o = mem_rdata_int;
    endcase
end

OBI_controller OBI_controller_inst (
    .clk                    ( clk_i ),
    .rst_n                  ( rst_n_i ),

    // Transaction request interface
    .core_rready_i          ( 1'b1 ),
    .core_valid_i           ( obi_req ),
    .core_ready_o           (  ),
    .core_addr_i            ( mem_addr_mem ),
    .core_we_i              ( mem_wen_mem ),
    .core_be_i              ( mem_ben_mem ),
    .core_wdata_i           ( mem_wdata_mem ),

    // Transaction response interface
    .resp_valid_o           ( mem_rvalid_mem ),
    .resp_rdata_o           ( mem_rdata_int ),
    .resp_err_o             (  ),

    // OBI interface
    .obi_req_o              ( data_obi_req_o ),
    .obi_gnt_i              ( data_obi_gnt_i ),
    .obi_addr_o             ( data_obi_addr_o ),
    .obi_we_o               ( data_obi_we_o ),
    .obi_be_o               ( data_obi_be_o ),
    .obi_wdata_o            ( data_obi_wdata_o ),
    .obi_atop_o             (  ),
    .obi_rdata_i            ( data_obi_rdata_i ),
    .obi_rready_o           ( data_obi_rready_o ),
    .obi_rvalid_i           ( data_obi_rvalid_i ),
    .obi_err_i              ( 1'b0 )

);

`ifdef JASPER
`default_nettype wire
`endif

endmodule