class bad_uvc_agent #(int XLEN=32, int ALEN=32) extends uvm_agent;

    bad_uvc_cfg   cfg;
    bad_uvc_cntxt cntxt;

    `uvm_component_utils_begin(bad_uvc_agent)
        `uvm_field_object(cfg  , UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end

    bad_uvc_vif     vif;
    bad_uvc_mon     monitor;
    bad_uvc_drv     driver;
    bad_uvc_seqr    sequencer;
    bad_uvc_cov     coverage;

    uvm_analysis_port #(bad_uvc_tr) item_from_monitor_port;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        item_from_monitor_port = new("item_from_monitor_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "vif", vif))
            `uvm_info("BAD_UVC AGENT", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("BAD_UVC AGENT", "No interface was set!")
        
        uvm_config_db#(bad_uvc_vif)::set(this, "*", "vif", vif);
        
        void'(uvm_config_db#(bad_uvc_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("BAD_UVC AGENT", "Config handle is null.")
        end      
        void'(uvm_config_db#(bad_uvc_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("BAD_UVC AGENT", "Context handle is null.")
        end
        
        uvm_config_db#(bad_uvc_cfg  )::set(this, "*", "cfg"  , cfg  );
        uvm_config_db#(bad_uvc_cntxt)::set(this, "*", "cntxt", cntxt);

        monitor       = bad_uvc_mon#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("monitor", this);
        if (cfg.is_active == UVM_ACTIVE) begin
            sequencer = bad_uvc_seqr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("sequencer", this);
            driver    = bad_uvc_drv #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("driver", this);
            `uvm_info("BAD_UVC AGENT", "Agent is active." , UVM_MEDIUM)
        end else begin
            `uvm_info("BAD_UVC AGENT", "Agent is not active." , UVM_MEDIUM)
        end

        if (cfg.cov_control == BAD_UVC_COV_ENABLE) begin
            coverage = bad_uvc_cov#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("coverage", this);
            `uvm_info("BAD_UVC AGENT", "Coverage is enabled." , UVM_MEDIUM) 
        end else begin
            `uvm_info("BAD_UVC AGENT", "Coverage is disabled." , UVM_MEDIUM)
        end
    endfunction: build_phase

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);

        monitor.item_collected_port.connect(item_from_monitor_port);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
            monitor.to_seqr_port.connect(sequencer.mon_tr_fifo.analysis_export);
        end

        if (cfg.cov_control == BAD_UVC_COV_ENABLE) begin
            monitor.item_collected_port.connect(coverage.analysis_export);
        end
    endfunction: connect_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("BAD_UVC AGENT", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

endclass: bad_uvc_agent
