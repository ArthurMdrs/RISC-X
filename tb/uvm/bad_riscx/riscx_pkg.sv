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
// Design Name:    RISC-X UVM package                                         //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Includes all RISC-X environment's files.                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package riscx_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import clknrst_pkg::*;
    import bad_uvc_pkg::*;
    import rvvi_pkg   ::*;

    `include "riscx_vseqr.sv"
    `include "riscx_vseq_lib.sv"
    `include "riscx_env.sv"
    
    `include "tests.sv"

endpackage: riscx_pkg