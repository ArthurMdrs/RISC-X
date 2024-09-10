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
// Design Name:    OBI configuration                                          //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    OBI configuration.                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class obi_cfg #(int XLEN=32, int ALEN=32) extends uvm_object;

    uvm_active_passive_enum is_active;
    obi_cov_enable_enum     cov_control;

    logic [ALEN-1:0] mem_start_addr = 1 << (ALEN-1);
    string           mem_bin_file;
    
    rand int unsigned gnt_latency_min;
    rand int unsigned gnt_latency_max;
   
    `uvm_object_param_utils_begin(obi_cfg#(XLEN, ALEN))
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(obi_cov_enable_enum, cov_control, UVM_ALL_ON)
        `uvm_field_int(mem_start_addr, UVM_ALL_ON)
        `uvm_field_int(gnt_latency_min, UVM_ALL_ON)
        `uvm_field_int(gnt_latency_max, UVM_ALL_ON)
    `uvm_object_utils_end

    constraint gnt_min_max {
        gnt_latency_min <= gnt_latency_max;
    }

    constraint gnt_no_big_latency {
        gnt_latency_max <= 20;
    }

    function new(string name = "obi_cfg");
        super.new(name);
        
        is_active = UVM_ACTIVE;
        cov_control = OBI_COV_ENABLE;
        
        if ($value$plusargs("start_addr=%h", mem_start_addr))
            `uvm_info("OBI CONFIG", $sformatf("Got memory start address from plusargs: 0x%h.", mem_start_addr), UVM_HIGH)
        // else
        //     `uvm_fatal("OBI CONFIG", $sformatf("%s %s", bin_file, error_desc))
        if ($value$plusargs("bin=%s", mem_bin_file))
            `uvm_info("OBI CONFIG", $sformatf("Got memory binary file path from plusargs: %s.", mem_bin_file), UVM_HIGH)
        else
            `uvm_fatal("OBI CONFIG", "A .bin file must be provided through plusargs!")
        
    endfunction: new
    
    function int unsigned get_rnd_gnt_latency();
        int unsigned latency;
        latency = $urandom_range(gnt_latency_min, gnt_latency_max);
        return latency;
    endfunction
   
endclass : obi_cfg