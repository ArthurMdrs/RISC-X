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
// Design Name:    OBI agent                                                  //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    OBI agent.                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class obi_agent #(int XLEN=32, int ALEN=32) extends uvm_agent;

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_component_param_utils_begin(obi_agent#(XLEN, ALEN))
        `uvm_field_object(cfg  , UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end

    obi_vif     vif;
    obi_mon     monitor;
    obi_drv     driver;
    obi_seqr    sequencer;
    obi_cov     coverage;

    uvm_analysis_port #(obi_tr) item_from_monitor_port;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        item_from_monitor_port = new("item_from_monitor_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", vif))
            `uvm_info("OBI AGENT", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("OBI AGENT", "No interface was set!")
        
        uvm_config_db#(obi_vif)::set(this, "*", "vif", vif);
        
        void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("OBI AGENT", "Config handle is null.")
        end      
        void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("OBI AGENT", "Context handle is null.")
        end
        
        uvm_config_db#(obi_cfg  )::set(this, "*", "cfg"  , cfg  );
        uvm_config_db#(obi_cntxt)::set(this, "*", "cntxt", cntxt);

        monitor       = obi_mon#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("monitor", this);
        if (cfg.is_active == UVM_ACTIVE) begin
            sequencer = obi_seqr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("sequencer", this);
            driver    = obi_drv #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("driver", this);
            `uvm_info("OBI AGENT", "Agent is active." , UVM_MEDIUM)
        end else begin
            `uvm_info("OBI AGENT", "Agent is not active." , UVM_MEDIUM)
        end

        if (cfg.cov_control == OBI_COV_ENABLE) begin
            coverage = obi_cov#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("coverage", this);
            `uvm_info("OBI AGENT", "Coverage is enabled." , UVM_MEDIUM) 
        end else begin
            `uvm_info("OBI AGENT", "Coverage is disabled." , UVM_MEDIUM)
        end
    endfunction: build_phase

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);

        monitor.item_collected_port.connect(item_from_monitor_port);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
            monitor.to_seqr_port.connect(sequencer.mon_tr_fifo.analysis_export);
        end

        if (cfg.cov_control == OBI_COV_ENABLE) begin
            monitor.item_collected_port.connect(coverage.analysis_export);
        end
    endfunction: connect_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI AGENT", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

endclass: obi_agent
