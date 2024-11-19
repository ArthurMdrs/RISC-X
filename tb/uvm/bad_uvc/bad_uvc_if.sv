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
// Design Name:    Bad UVC interface                                          //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bad UVC interface.                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

interface bad_uvc_if #(int XLEN=32, int ALEN=32) (input clk, input rst_n);

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import bad_uvc_pkg::*;

    // Address phase signals
    logic [ALEN  -1:0] addr;
    logic              we;
    logic [XLEN/8-1:0] be;
    logic [XLEN  -1:0] wdata;
    
    // Response phase signals
    logic [XLEN  -1:0] rdata;
    
    // Indicates that the monitor should be collecting transactions
    bit addr_mon_active = 0;
    bit resp_mon_active = 0;

    task bad_uvc_reset_sigs();
        rdata <= '0;
    endtask
    
    task addr_ch_collect_tr(bad_uvc_tr tr);
        tr.addr = addr;
        tr.we = we;
        tr.be = be;
        tr.wdata = wdata;
    endtask : addr_ch_collect_tr
    
    task resp_ch_collect_tr(bad_uvc_tr tr);
        tr.rdata = rdata;
    endtask : resp_ch_collect_tr
    
    task resp_ch_drive_tr(bad_uvc_tr tr);
        rdata <= tr.rdata;
        
        // @(posedge clk);
        @(negedge clk);
    endtask : resp_ch_drive_tr
    
    task resp_ch_reset_sigs();
        rdata <= '0;
    endtask : resp_ch_reset_sigs
    
    task wait_clk_posedge();
        @(posedge clk);
    endtask : wait_clk_posedge
    
    task wait_clk_negedge();
        @(negedge clk);
    endtask : wait_clk_negedge
    
    task wait_rst_assertion();
        wait(rst_n === 1'b0);
    endtask : wait_rst_assertion
    
    task wait_rst_deassertion();
        wait(rst_n === 1'b1);
    endtask : wait_rst_deassertion
    
    function void set_addr_mon_active_val(bit val);
        addr_mon_active = val;
    endfunction : set_addr_mon_active_val
    
    function void set_resp_mon_active_val(bit val);
        resp_mon_active = val;
    endfunction : set_resp_mon_active_val
        
endinterface : bad_uvc_if
