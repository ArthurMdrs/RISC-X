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
// Design Name:    Clock and reset coverage                                   //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset coverage.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class clknrst_cov extends uvm_subscriber #(clknrst_tr);

    clknrst_cfg cfg;

    real coverage_value;
    clknrst_tr cov_transaction;

    `uvm_component_utils_begin(clknrst_cov)
        `uvm_field_object(cfg, UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_real(coverage_value, UVM_ALL_ON)
    `uvm_component_utils_end

    covergroup clknrst_covergroup;
        option.per_instance = 1;
        option.name = {get_full_name(), ".", "covergroup"};
        // option.at_least = 3;
        // option.auto_bin_max = 256;
        // option.cross_auto_bin_max = 256;
    endgroup : clknrst_covergroup

    function new (string name, uvm_component parent);
        super.new(name, parent);
        clknrst_covergroup = new();
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST COVERAGE", "Configuration object was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST COVERAGE", "No configuration object was set!")
    endfunction: build_phase

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("CLKNRST COVERAGE", $sformatf("Coverage: %2.2f%%", get_coverage()), UVM_NONE)
    endfunction : report_phase

    function void sample (clknrst_tr t);
        cov_transaction = t;
        clknrst_covergroup.sample();
    endfunction : sample

    function real get_coverage ();
        return clknrst_covergroup.get_inst_coverage();
    endfunction : get_coverage

    function void write(clknrst_tr t);      
        sample(t); // sample coverage with this transaction
        coverage_value = get_coverage();
    endfunction : write

endclass : clknrst_cov
