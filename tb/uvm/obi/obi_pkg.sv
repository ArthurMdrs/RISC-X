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
// Design Name:    OBI package                                                //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Includes all OBI agent's files.                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package obi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "riscx_mem_model.sv"
    
    `include "obi_tdefs.sv"

    typedef virtual interface obi_if obi_vif;

    `include "obi_cntxt.sv"
    `include "obi_cfg.sv"
    `include "obi_tr.sv"
    `include "obi_seqr.sv"
    `include "obi_seq_lib.sv"
    `include "obi_mon.sv"
    `include "obi_drv.sv"
    `include "obi_cov.sv"
    `include "obi_agent.sv"

endpackage: obi_pkg
