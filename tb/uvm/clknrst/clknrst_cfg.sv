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
// Design Name:    Clock and reset configuration                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset configuration.                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class clknrst_cfg extends uvm_object;

    uvm_active_passive_enum is_active;
    clknrst_cov_enable_enum cov_control;
    
    rand clknrst_init_val_enum initial_rst_val;

    `uvm_object_utils_begin(clknrst_cfg)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(clknrst_cov_enable_enum, cov_control, UVM_ALL_ON)
        `uvm_field_enum(clknrst_init_val_enum, initial_rst_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new (string name = "clknrst_cfg");
        super.new(name);
        is_active = UVM_ACTIVE;
        cov_control = CLKNRST_COV_ENABLE;
        initial_rst_val = CLKNRST_INITIAL_VALUE_1;
    endfunction: new

endclass: clknrst_cfg
