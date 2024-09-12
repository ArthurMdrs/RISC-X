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
// Design Name:    Bad UVC package                                            //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Includes all Bad UVC agent's files.                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package bad_uvc_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "riscx_mem_model.sv"
    
    `include "bad_uvc_tdefs.sv"

    typedef virtual interface bad_uvc_if bad_uvc_vif;

    `include "bad_uvc_cntxt.sv"
    `include "bad_uvc_cfg.sv"
    `include "bad_uvc_tr.sv"
    `include "bad_uvc_seqr.sv"
    `include "bad_uvc_seq_lib.sv"
    `include "bad_uvc_mon.sv"
    `include "bad_uvc_drv.sv"
    `include "bad_uvc_cov.sv"
    `include "bad_uvc_agent.sv"

endpackage: bad_uvc_pkg
