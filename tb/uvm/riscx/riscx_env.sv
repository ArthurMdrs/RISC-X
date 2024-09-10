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
// Design Name:    RISC-X UVM environment                                     //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RISC-X UVM Environent. Instantiates agents, creates and    //
//                 sets config and context objects, sets virtual interfaces   //
//                 for the agents.                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class riscx_env extends uvm_env;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    // clknrst_cfg   cfg_clknrst;
    // // clknrst_cntxt cntxt_clknrst;
    // clknrst_vif   vif_clknrst;

    obi_cfg   instr_obi_cfg;
    obi_cntxt instr_obi_cntxt;
    obi_vif   instr_obi_vif;

    // obi_cfg   data_obi_cfg;
    // obi_cntxt data_obi_cntxt;
    // obi_vif   data_obi_vif;

    `uvm_component_utils_begin(riscx_env)
    //   `uvm_field_object(cfg_clknrst   , UVM_ALL_ON)
    // //   `uvm_field_object(cntxt_clknrst , UVM_ALL_ON)
      `uvm_field_object(instr_obi_cfg  , UVM_ALL_ON)
      `uvm_field_object(instr_obi_cntxt, UVM_ALL_ON)
    //   `uvm_field_object(data_obi_cfg   , UVM_ALL_ON)
    //   `uvm_field_object(data_obi_cntxt , UVM_ALL_ON)
    `uvm_component_utils_end

    // clknrst_agent agent_clknrst;
    obi_agent     instr_obi_agent;
    // obi_agent     data_obi_agent;
    
    riscx_vseqr vsequencer;

    // uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        // if(uvm_config_db#(clknrst_vif)::get(this, "", "vif_clknrst", vif_clknrst))
        //     `uvm_info("RISC-X ENV", "Virtual interface for clknrst was successfully set!", UVM_HIGH)
        // else
        //     `uvm_error("RISC-X ENV", "No interface for clknrst was set!")
        if(uvm_config_db#(obi_vif)::get(this, "", "instr_obi_vif", instr_obi_vif))
            `uvm_info("RISC-X ENV", "Virtual interface for Instr OBI was successfully set!", UVM_HIGH)
        else
            `uvm_error("RISC-X ENV", "No interface for Instr OBI was set!")
        // if(uvm_config_db#(obi_vif)::get(this, "", "data_obi_vif", data_obi_vif))
        //     `uvm_info("RISC-X ENV", "Virtual interface for Data OBI was successfully set!", UVM_HIGH)
        // else
        //     `uvm_error("RISC-X ENV", "No interface for Data OBI was set!")
        
        // uvm_config_db#(clknrst_vif)::set(this, "agent_clknrst"  , "vif", vif_clknrst  );
        uvm_config_db#(obi_vif    )::set(this, "instr_obi_agent", "vif", instr_obi_vif);
        // uvm_config_db#(obi_vif    )::set(this, "data_obi_agent" , "vif", data_obi_vif );
        
        // cfg_clknrst     = clknrst_cfg                        ::type_id::create("cfg_clknrst"    );
        // // cntxt_clknrst   = clknrst_cntxt                      ::type_id::create("cntxt_clknrst"  );
        instr_obi_cfg   = obi_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cfg"  );
        instr_obi_cntxt = obi_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cntxt");
        // data_obi_cfg    = obi_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_obi_cfg"   );
        // data_obi_cntxt  = obi_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_obi_cntxt" );
        
        instr_obi_cfg.gnt_latency_min = 0;
        instr_obi_cfg.gnt_latency_max = 10;
        // data_obi_cfg.gnt_latency_min = 0;
        // data_obi_cfg.gnt_latency_max = 10;
        // data_obi_cntxt.mem = instr_obi_cntxt.mem;
        
        // cfg_clknrst.cov_control   = CLKNRST_COV_DISABLE;
        instr_obi_cfg.cov_control = OBI_COV_DISABLE;
        // data_obi_cfg.cov_control  = OBI_COV_DISABLE;
        
        // uvm_config_db#(clknrst_cfg)::set(this, "agent_clknrst"  , "cfg"  , cfg_clknrst    );
        // // uvm_config_db#(clknrst_cntxt)::set(this, "agent_clknrst"      , "cntxt", cntxt_clknrst      );
        uvm_config_db#(obi_cfg    )::set(this, "instr_obi_agent", "cfg"  , instr_obi_cfg  );
        uvm_config_db#(obi_cntxt  )::set(this, "instr_obi_agent", "cntxt", instr_obi_cntxt);
        // uvm_config_db#(obi_cfg    )::set(this, "data_obi_agent" , "cfg"  , data_obi_cfg   );
        // uvm_config_db#(obi_cntxt  )::set(this, "data_obi_agent" , "cntxt", data_obi_cntxt );

        // agent_clknrst   = clknrst_agent                      ::type_id::create("agent_clknrst"  , this);
        instr_obi_agent = obi_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_agent", this);
        // data_obi_agent  = obi_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_obi_agent" , this);
        
        vsequencer = riscx_vseqr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("vsequencer", this);

        `uvm_info("RISC-X ENV", "Build phase running", UVM_HIGH)
        // uvm_config_db#(int)::set(this, "*", "recording_detail", 1);
    endfunction

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        
        // vsequencer.sequencer_clknrst = agent_clknrst  .sequencer;
        vsequencer.instr_obi_seqr    = instr_obi_agent.sequencer;
        // vsequencer.data_obi_seqr     = data_obi_agent .sequencer;
    endfunction: connect_phase

endclass: riscx_env
