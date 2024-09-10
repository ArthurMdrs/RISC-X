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
// Design Name:    OBI coverage                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    OBI coverage.                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class obi_cov #(int XLEN=32, int ALEN=32) extends uvm_subscriber #(obi_tr#(.XLEN(XLEN),.ALEN(ALEN)));

    obi_cfg   cfg;
    obi_cntxt cntxt;

    real cov_val;
    obi_tr cov_transaction;

    `uvm_component_param_utils_begin(obi_cov#(XLEN, ALEN))
        `uvm_field_object(cfg  , UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_object(cntxt, UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_real(cov_val, UVM_ALL_ON)
    `uvm_component_utils_end

    covergroup obi_covergroup;
        option.per_instance = 1;
        option.name = {get_full_name(), ".", "covergroup"};
        // option.at_least = 3;
        // option.auto_bin_max = 256;
        // option.cross_auto_bin_max = 256;
        cp_gnt_latency: coverpoint cov_transaction.gnt_latency;
        cp_rvalid_latency: coverpoint cov_transaction.rvalid_latency;
        cp_addr: coverpoint cov_transaction.addr;
        cp_we: coverpoint cov_transaction.we;
        cp_be: coverpoint cov_transaction.be;
        cp_wdata: coverpoint cov_transaction.wdata;
        cp_rdata: coverpoint cov_transaction.rdata;
    endgroup : obi_covergroup

    function new (string name, uvm_component parent);
        super.new(name, parent);
        obi_covergroup = new();
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("OBI SEQUENCER", "Config handle is null.")
        end      
        void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("OBI SEQUENCER", "Context handle is null.")
        end      
    endfunction: build_phase

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("OBI COVERAGE", $sformatf("Coverage: %2.2f%%", get_coverage()), UVM_NONE)
    endfunction : report_phase

    function void sample (obi_tr t);
        cov_transaction = t;
        obi_covergroup.sample();
    endfunction : sample

    function real get_coverage ();
        return obi_covergroup.get_inst_coverage();
    endfunction : get_coverage

    function void write(obi_tr t);      
        sample(t); // sample coverage with this transaction
        cov_val = get_coverage();
    endfunction : write

endclass : obi_cov
