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
// Design Name:    Clock and reset transaction                                //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset transaction.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class clknrst_tr extends uvm_sequence_item;
    
    rand clknrst_action_enum   action;
    rand int unsigned          rst_assert_duration;     // In ps
    rand int unsigned          clk_period;              // In ps
    rand clknrst_init_val_enum initial_clk_val;
    
    `uvm_object_utils_begin(clknrst_tr)
        `uvm_field_enum(clknrst_action_enum  , action         , UVM_ALL_ON)
        `uvm_field_int (rst_assert_duration                   , UVM_ALL_ON)
        `uvm_field_int (clk_period                            , UVM_ALL_ON)
        `uvm_field_enum(clknrst_init_val_enum, initial_clk_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="clknrst_tr");
        super.new(name);
    endfunction: new

    constraint max_clk_period {
        clk_period <= 20_000; // 20ns
    }

    constraint max_rst_assert_duration {
        rst_assert_duration <= 15_000; // 15ns
    }

endclass: clknrst_tr
