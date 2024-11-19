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
// Design Name:    Bad UVC context                                            //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bad UVC context.                                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class bad_uvc_cntxt #(int XLEN=32, int ALEN=32) extends uvm_object;

    riscx_mem_model mem;

    bad_uvc_reset_state_enum rst_state = BAD_UVC_RST_STATE_PRE_RESET;
   
    `uvm_object_utils_begin(bad_uvc_cntxt)
        `uvm_field_enum(bad_uvc_reset_state_enum, rst_state, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "bad_uvc_cntxt");
        super.new(name);
        
        mem = riscx_mem_model#(ALEN)::type_id::create("mem");
    endfunction: new
   
endclass : bad_uvc_cntxt