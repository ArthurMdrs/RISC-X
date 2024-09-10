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
// Design Name:    RVVI monitor                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVVI monitor.                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class rvvi_mon #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_monitor;

    rvvi_cfg cfg;

    `uvm_component_param_utils_begin(rvvi_mon#(ILEN,XLEN,FLEN))
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end

    rvvi_vif vif; // TODO: does this have to be parameterized?
    rvvi_tr tr;
    int num_tr_col;

    uvm_analysis_port #(rvvi_tr#(ILEN,XLEN,FLEN)) item_collected_port;
    uvm_analysis_port #(bit [ILEN-1:0])           detected_insn_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
        detected_insn_port  = new("detected_insn_port" , this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
            
        if(uvm_config_db#(rvvi_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("RVVI MONITOR", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI MONITOR", "No configuration object was set!")
        
        if(uvm_config_db#(rvvi_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("RVVI MONITOR", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI MONITOR", "No interface was set!")
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        @(negedge vif.rst_n);
        @(posedge vif.rst_n);

        `uvm_info("RVVI MONITOR", "Reset dropped", UVM_LOW)

        forever begin
            tr = rvvi_tr#(ILEN,XLEN,FLEN)::type_id::create("tr", this);
            
            void'(begin_tr(tr, "RVVI_MONITOR_TR"));
            
            vif.collect_tr(tr);
            item_collected_port.write(tr);
            
            if (cfg.detect_insn) begin
                if (tr.insn == cfg.detect_insn_val) begin
                    `uvm_info("RVVI MONITOR", $sformatf("Detected instruction 0x%h.", tr.insn), UVM_MEDIUM)
                    detected_insn_port.write(tr.insn);
                end
            end
            
            vif.wait_clk();

            end_tr(tr);
            `uvm_info("RVVI MONITOR", $sformatf("Transaction Collected:\n%s", tr.convert2string()), UVM_LOW)
            num_tr_col++;
        end
    endtask : run_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("RVVI MONITOR", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("RVVI MONITOR", $sformatf("Report: RVVI MONITOR collected %0d transactions", num_tr_col), UVM_LOW)
    endfunction : report_phase

endclass: rvvi_mon
