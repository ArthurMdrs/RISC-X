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
// Design Name:    Testbench top                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Testbench top module that runs an UVM test.                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module tb_top;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import riscx_pkg::*;

    bit clk, rst_n;
    bit run_clock;

    // Interfaces instances - begin
        obi_if if_obi(.clk(clk), .rst_n(rst_n));
    // Interfaces instances - end
    assign if_obi.rready = 1'b1;

    stub dut(
        .clk(clk),
        .rst_n(rst_n),
        // Signals from obi's interface - begin
            .req_o(if_obi.req),
            .gnt_i(if_obi.gnt),
            .addr_o(if_obi.addr),
            .we_o(if_obi.we),
            .be_o(if_obi.be),
            .wdata_o(if_obi.wdata),
            .rvalid_i(if_obi.rvalid),
            .rdata_i(if_obi.rdata)
        // Signals from obi's interface - end
    );
    
    // uvm_default_report_server rserver;

    initial begin
        clk = 0;
        rst_n = 1;
        #3 rst_n = 0;
        #3 rst_n = 1;
    end
    always #2 clk=~clk;

    initial begin
        $timeformat(-9, 3, "ns", 12); // e.g.: "       900ns"
        $dumpfile("dump.vcd");
        $dumpvars;
        
        
        // rserver = uvm_report_server::get_server();

        // Virtual interfaces send to VIPs - begin
            uvm_config_db#(virtual interface obi_if)::set(null, "uvm_test_top", "vif", if_obi);
        // Virtual interfaces send to VIPs - end

        run_test("random_test");
    end

endmodule: tb_top
