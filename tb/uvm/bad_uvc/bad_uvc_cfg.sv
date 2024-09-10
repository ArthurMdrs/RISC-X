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
// Design Name:    Bad UVC configuration                                      //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bad UVC configuration.                                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class bad_uvc_cfg #(int XLEN=32, int ALEN=32) extends uvm_object;

    uvm_active_passive_enum is_active;
    bad_uvc_cov_enable_enum cov_control;

    logic [ALEN-1:0] mem_start_addr = 1 << (ALEN-1);
    string mem_bin_file;
   
    `uvm_object_param_utils_begin(bad_uvc_cfg)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(bad_uvc_cov_enable_enum, cov_control, UVM_ALL_ON)
        `uvm_field_int(mem_start_addr, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "bad_uvc_cfg");
        super.new(name);
        
        is_active = UVM_ACTIVE;
        cov_control = BAD_UVC_COV_ENABLE;
        
        if ($value$plusargs("start_addr=%h", mem_start_addr))
            `uvm_info("BAD_UVC CONFIG", $sformatf("Got memory start address from plusargs: 0x%h.", mem_start_addr), UVM_HIGH)
        // else
        //     `uvm_fatal("BAD_UVC CONFIG", $sformatf("%s %s", bin_file, error_desc))
        if ($value$plusargs("bin=%s", mem_bin_file))
            `uvm_info("BAD_UVC CONFIG", $sformatf("Got memory binary file path from plusargs: %s.", mem_bin_file), UVM_HIGH)
        else
            `uvm_fatal("BAD_UVC CONFIG", "A .bin file must be provided through plusargs!")
        
    endfunction: new
   
endclass : bad_uvc_cfg