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
// Design Name:    Clock and reset interface                                  //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset interface.                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

interface clknrst_if ();
    
    import uvm_pkg::*;    
    `include "uvm_macros.svh"
    import clknrst_pkg::*;
    
    logic clk;
    logic rst_n;
    
    realtime clk_period = 10ns;
    bit      clk_active;
    
    // Generate clock
    initial begin
        wait (clk_active);
        forever begin
            #(clk_period);
            if (clk_active) begin
                case (clk)
                1'b0: clk = 1'b1;
                1'b1: clk = 1'b0;
                1'bx: clk = 1'b0;
                endcase
            end
        end
    end
    
    function void set_period(realtime new_clk_period);
        `uvm_info("CLKNRST INTERFACE", $sformatf("Changing clock period to %0t", new_clk_period), UVM_LOW)
        clk_period = new_clk_period;
    endfunction : set_period
    
    function void start_clk();
        `uvm_info("CLKNRST INTERFACE", "Starting clock generation", UVM_HIGH)
        if (clk_period != 0ns)
            clk_active = 1;
    endfunction : start_clk
    
    task stop_clk();
        `uvm_info("CLKNRST INTERFACE", "Stopping clock generation", UVM_HIGH)
        wait (clk == 1'b0);
        clk_active = 0;
    endtask : stop_clk
    
    function void set_clk_val(logic new_clk_val);
        `uvm_info("CLKNRST INTERFACE", $sformatf("Changing clock value to %b", new_clk_val), UVM_HIGH)
        clk = new_clk_val;
    endfunction : set_clk_val
    
    function void set_rst_val(logic new_rst_val);
        `uvm_info("CLKNRST INTERFACE", $sformatf("Changing reset value to %b", new_rst_val), UVM_HIGH)
        rst_n = new_rst_val;
    endfunction : set_rst_val
    
    task assert_rst(int unsigned rst_assert_duration);
        `uvm_info("CLKNRST INTERFACE", $sformatf("Asserting reset for %0t", (rst_assert_duration * 1ps)), UVM_MEDIUM)
        rst_n = 1'b0;
        #(rst_assert_duration * 1ps);
        `uvm_info("CLKNRST INTERFACE", "De-asserting reset", UVM_MEDIUM)
        rst_n = 1'b1;
    endtask : assert_rst
    
    task wait_clk_posedge();
        @(posedge clk);
    endtask : wait_clk_posedge
    
    task wait_clk_negedge();
        @(negedge clk);
    endtask : wait_clk_negedge

endinterface : clknrst_if
