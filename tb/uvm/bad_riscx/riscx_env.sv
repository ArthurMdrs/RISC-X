class riscx_env extends uvm_env;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    clknrst_cfg   cfg_clknrst;
    // clknrst_cntxt cntxt_clknrst;
    clknrst_vif   vif_clknrst;

    bad_uvc_cfg   instr_bad_uvc_cfg;
    bad_uvc_cntxt instr_bad_uvc_cntxt;
    bad_uvc_vif   instr_bad_uvc_vif;

    bad_uvc_cfg   data_bad_uvc_cfg;
    bad_uvc_cntxt data_bad_uvc_cntxt;
    bad_uvc_vif   data_bad_uvc_vif;

    `uvm_component_utils_begin(riscx_env)
      `uvm_field_object(cfg_clknrst   , UVM_ALL_ON)
    //   `uvm_field_object(cntxt_clknrst , UVM_ALL_ON)
      `uvm_field_object(instr_bad_uvc_cfg  , UVM_ALL_ON)
      `uvm_field_object(instr_bad_uvc_cntxt, UVM_ALL_ON)
      `uvm_field_object(data_bad_uvc_cfg   , UVM_ALL_ON)
      `uvm_field_object(data_bad_uvc_cntxt , UVM_ALL_ON)
    `uvm_component_utils_end

    clknrst_agent agent_clknrst;
    bad_uvc_agent instr_bad_uvc_agent;
    bad_uvc_agent data_bad_uvc_agent;
    
    riscx_vseqr vsequencer;

    // uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(clknrst_vif)::get(this, "", "vif_clknrst", vif_clknrst))
            `uvm_info("RISC-X ENV", "Virtual interface for clknrst was successfully set!", UVM_HIGH)
        else
            `uvm_error("RISC-X ENV", "No interface for clknrst was set!")
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "instr_bad_uvc_vif", instr_bad_uvc_vif))
            `uvm_info("RISC-X ENV", "Virtual interface for Instr bad_uvc was successfully set!", UVM_HIGH)
        else
            `uvm_error("RISC-X ENV", "No interface for Instr bad_uvc was set!")
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "data_bad_uvc_vif", data_bad_uvc_vif))
            `uvm_info("RISC-X ENV", "Virtual interface for Data bad_uvc was successfully set!", UVM_HIGH)
        else
            `uvm_error("RISC-X ENV", "No interface for Data bad_uvc was set!")
        
        uvm_config_db#(clknrst_vif)::set(this, "agent_clknrst"      , "vif", vif_clknrst      );
        uvm_config_db#(bad_uvc_vif)::set(this, "instr_bad_uvc_agent", "vif", instr_bad_uvc_vif);
        uvm_config_db#(bad_uvc_vif)::set(this, "data_bad_uvc_agent" , "vif", data_bad_uvc_vif );
        
        cfg_clknrst         = clknrst_cfg                            ::type_id::create("cfg_clknrst"        );
        // cntxt_clknrst       = clknrst_cntxt                          ::type_id::create("cntxt_clknrst"      );
        instr_bad_uvc_cfg   = bad_uvc_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_bad_uvc_cfg"  );
        instr_bad_uvc_cntxt = bad_uvc_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_bad_uvc_cntxt");
        data_bad_uvc_cfg    = bad_uvc_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_bad_uvc_cfg"   );
        data_bad_uvc_cntxt  = bad_uvc_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_bad_uvc_cntxt" );
        
        data_bad_uvc_cntxt.mem = instr_bad_uvc_cntxt.mem;
        
        cfg_clknrst.cov_control       = CLKNRST_COV_DISABLE;
        instr_bad_uvc_cfg.cov_control = BAD_UVC_COV_DISABLE;
        data_bad_uvc_cfg.cov_control  = BAD_UVC_COV_DISABLE;
        
        uvm_config_db#(clknrst_cfg  )::set(this, "agent_clknrst"      , "cfg"  , cfg_clknrst        );
        // uvm_config_db#(clknrst_cntxt)::set(this, "agent_clknrst"      , "cntxt", cntxt_clknrst      );
        uvm_config_db#(bad_uvc_cfg  )::set(this, "instr_bad_uvc_agent", "cfg"  , instr_bad_uvc_cfg  );
        uvm_config_db#(bad_uvc_cntxt)::set(this, "instr_bad_uvc_agent", "cntxt", instr_bad_uvc_cntxt);
        uvm_config_db#(bad_uvc_cfg  )::set(this, "data_bad_uvc_agent" , "cfg"  , data_bad_uvc_cfg   );
        uvm_config_db#(bad_uvc_cntxt)::set(this, "data_bad_uvc_agent" , "cntxt", data_bad_uvc_cntxt );

        agent_clknrst       = clknrst_agent                          ::type_id::create("agent_clknrst"      , this);
        instr_bad_uvc_agent = bad_uvc_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_bad_uvc_agent", this);
        data_bad_uvc_agent  = bad_uvc_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("data_bad_uvc_agent" , this);
        
        vsequencer = riscx_vseqr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("vsequencer", this);

        `uvm_info("RISC-X ENV", "Build phase running", UVM_HIGH)
        // uvm_config_db#(int)::set(this, "*", "recording_detail", 1);
    endfunction

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        
        vsequencer.sequencer_clknrst  = agent_clknrst      .sequencer;
        vsequencer.instr_bad_uvc_seqr = instr_bad_uvc_agent.sequencer;
        vsequencer.data_bad_uvc_seqr  = data_bad_uvc_agent .sequencer;
    endfunction: connect_phase

endclass: riscx_env
