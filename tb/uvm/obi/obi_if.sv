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
// Design Name:    OBI interface                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    OBI interface.                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

interface obi_if #(int XLEN=32, int ALEN=32) (input clk, input rst_n);

    import uvm_pkg::*;    
    `include "uvm_macros.svh"
    import obi_pkg::*;

    // Address phase signals
    logic              req;
    logic              gnt;
    logic [ALEN  -1:0] addr;
    logic              we;
    logic [XLEN/8-1:0] be;
    logic [XLEN  -1:0] wdata;
    
    // Response phase signals
    logic              rvalid;
    logic              rready;
    logic [XLEN  -1:0] rdata;

    task obi_reset_sigs();
        gnt <= 1'b0;
        rvalid <= 1'b0;
        rdata <= '0;
    endtask
    
    task addr_ch_collect_tr(obi_tr tr);
        int unsigned latency;
        
        while (!(req===1'b1)) begin
            @(posedge clk);
        end
        latency = 0;
        while (!(req===1'b1 && gnt===1'b1)) begin
            @(posedge clk);
            latency++;
        end
        
        tr.addr = addr;
        tr.we = we;
        tr.be = be;
        tr.wdata = wdata;
        tr.gnt_latency = latency;
        
        // @(posedge clk);
    endtask : addr_ch_collect_tr
    
    task resp_ch_collect_tr(obi_tr tr);
        int unsigned latency;
        
        latency = 0;
        while (!(rvalid===1'b1 && rready===1'b1)) begin
            @(posedge clk);
            // latency++; // TODO: fix latency count
        end
        
        tr.rdata = rdata;
        tr.rvalid_latency = latency;
        
        // @(posedge clk);
    endtask : resp_ch_collect_tr
    
    // task addr_ch_drive_tr(obi_tr tr);
    task addr_ch_drive_tr(int unsigned gnt_latency);
        int unsigned wait_gnt_cycles;
        wait_gnt_cycles = gnt_latency;
        gnt <= 1'b0;
        
        do begin
            if (gnt_latency == 0) // if true, we're in the last cycle of waiting
                gnt <= 1'b1;
            @(posedge clk);
            if (req===1'b1 && gnt_latency != 0)
                gnt_latency--;
        end while (!(req===1'b1 && gnt===1'b1));
        
        gnt <= 1'b0;
    endtask : addr_ch_drive_tr
    
    task resp_ch_drive_tr(obi_tr tr);
        rvalid <= 1'b0;
        
        repeat (tr.rvalid_latency) begin
            @(posedge clk);
        end
        
        rvalid <= 1'b1;
        rdata <= tr.rdata;
        
        while (rready!==1'b1) begin
            @(posedge clk);
        end
        
        @(posedge clk);
        rvalid <= 1'b0;
    endtask : resp_ch_drive_tr
    
    task addr_ch_reset_sigs();
        gnt <= 1'b0;
    endtask : addr_ch_reset_sigs
    
    task resp_ch_reset_sigs();
        rvalid <= 1'b0;
        rdata <= '0;
    endtask : resp_ch_reset_sigs
    
    task wait_clk();
        @(posedge clk);
    endtask : wait_clk
    
    assert property (@(posedge clk) disable iff (!rst_n) req |-> ##[1:$] gnt);
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(addr)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(we)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(be)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(wdata)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> req));

    assert property (@(posedge clk) disable iff (!rst_n) rvalid |-> ##[1:$] rready);
    assert property (@(posedge clk) disable iff (!rst_n) (rvalid && !rready |=> $stable(rdata)));
    assert property (@(posedge clk) disable iff (!rst_n) (rvalid && !rready |=> rvalid));
        
endinterface : obi_if
