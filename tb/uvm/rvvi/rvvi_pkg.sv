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
// Design Name:    RVVI package                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Includes all RVVI agent's files.                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package rvvi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // We use csr_addr_t from core_pkg in the tr_log
    import core_pkg::*;
    
    `include "rvvi_tdefs.sv"

    typedef virtual interface rvvi_if rvvi_vif;

    `include "rvvi_cfg.sv"
    `include "rvvi_tr.sv"
    `include "rvvi_sqr.sv"
    `include "rvvi_seq_lib.sv"
    `include "rvvi_mon.sv"
    `include "rvvi_drv.sv"
    `include "rvvi_cov.sv"
    `include "rvvi_tr_log.sv"
    `include "rvvi_agent.sv"

endpackage: rvvi_pkg
