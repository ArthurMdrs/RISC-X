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
// Design Name:    RVVI configuration                                         //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVVI configuration.                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class rvvi_cfg #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_object;

    uvm_active_passive_enum  is_active;
    rvvi_cov_enable_enum     cov_control;
    rvvi_logging_enable_enum log_control;
    
    // If detect_insn = 1, the monitor will check if detect_insn_val shows up in the interface
    // Can be used to catch ecall and detect the end of a test
    bit            detect_insn;
    bit [ILEN-1:0] detect_insn_val;
    
    string log_file;

    `uvm_object_param_utils_begin(rvvi_cfg#(ILEN,XLEN,FLEN))
        `uvm_field_enum(uvm_active_passive_enum , is_active      , UVM_ALL_ON)
        `uvm_field_enum(rvvi_cov_enable_enum    , cov_control    , UVM_ALL_ON)
        `uvm_field_enum(rvvi_logging_enable_enum, log_control    , UVM_ALL_ON)
        `uvm_field_int (                          detect_insn    , UVM_ALL_ON)
        `uvm_field_int (                          detect_insn_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new (string name = "rvvi_cfg");
        super.new(name);
        
        is_active = UVM_ACTIVE;
        cov_control = RVVI_COV_ENABLE;
        log_control = RVVI_LOGGING_ENABLE;
        
        detect_insn = 0;
        detect_insn_val = '0;
        
        if ($value$plusargs("rvvi_log=%s", log_file)) begin
            `uvm_info("RVVI CONFIG", $sformatf("Got log file path from plusargs: %s.", log_file), UVM_LOW)
        end
        else begin
            log_file = "rvvi_instr_trace.log";
            `uvm_info("RVVI CONFIG", $sformatf("Instruction trace will be saved to: %s.", log_file), UVM_LOW)
        end
    endfunction: new

endclass: rvvi_cfg
