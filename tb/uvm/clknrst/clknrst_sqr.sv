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
// Design Name:    Clock and reset sequencer                                  //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset sequencer.                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class clknrst_sqr extends uvm_sequencer#(clknrst_tr);

    clknrst_cfg cfg;

    `uvm_component_utils_begin(clknrst_sqr)
        `uvm_field_object(cfg, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end
    
    clknrst_vif vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST SEQUENCER", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("CLKNRST SEQUENCER", "No configuration object was set!")
        
        if(uvm_config_db#(clknrst_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("CLKNRST SEQUENCER", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("CLKNRST SEQUENCER", "No interface was set!")
    endfunction: build_phase

endclass: clknrst_sqr
