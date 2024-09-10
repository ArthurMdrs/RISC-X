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
// Design Name:    Clock and reset package                                    //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Includes all clock and reset agent's files.                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package clknrst_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // import clknrst_tdefs_pkg::*;
    `include "clknrst_tdefs.sv"

    typedef virtual interface clknrst_if clknrst_vif;

    `include "clknrst_cfg.sv"
    `include "clknrst_tr.sv"
    `include "clknrst_sqr.sv"
    `include "clknrst_seq_lib.sv"
    `include "clknrst_mon.sv"
    `include "clknrst_drv.sv"
    `include "clknrst_cov.sv"
    `include "clknrst_agent.sv"

endpackage: clknrst_pkg
