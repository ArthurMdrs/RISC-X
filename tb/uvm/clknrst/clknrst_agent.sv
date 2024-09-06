class clknrst_agent extends uvm_agent;

    clknrst_cfg cfg;

    `uvm_component_utils_begin(clknrst_agent)
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end

    clknrst_vif vif;
    clknrst_mon monitor;
    clknrst_drv driver;
    clknrst_sqr sequencer;
    clknrst_cov coverage;

    uvm_analysis_port #(clknrst_tr) item_from_monitor_port;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        item_from_monitor_port = new("item_from_monitor_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST AGENT", "Configuration object was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST AGENT", "No configuration object was set!")
        uvm_config_db#(clknrst_cfg)::set(.cntxt(this), .inst_name("*"), .field_name("cfg"), .value(cfg));
        
        if(uvm_config_db#(clknrst_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("CLKNRST AGENT", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST AGENT", "No interface was set!")
        uvm_config_db#(clknrst_vif)::set(.cntxt(this), .inst_name("*"), .field_name("vif"), .value(vif));
        
        monitor       = clknrst_mon::type_id::create("monitor", this);
        if (cfg.is_active == UVM_ACTIVE) begin
            sequencer = clknrst_sqr::type_id::create("sequencer", this);
            driver    = clknrst_drv::type_id::create("driver", this);
            `uvm_info("CLKNRST AGENT", "Agent is active." , UVM_MEDIUM)
        end else begin
            `uvm_info("CLKNRST AGENT", "Agent is not active." , UVM_MEDIUM)
        end

        if (cfg.cov_control == CLKNRST_COV_ENABLE) begin
            coverage = clknrst_cov::type_id::create("coverage", this);
            `uvm_info("CLKNRST AGENT", "Coverage is enabled." , UVM_MEDIUM)
        end else begin
            `uvm_info("CLKNRST AGENT", "Coverage is disabled." , UVM_MEDIUM)
        end
    endfunction: build_phase

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);

        monitor.item_collected_port.connect(item_from_monitor_port);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end

        if (cfg.cov_control == CLKNRST_COV_ENABLE) begin
            monitor.item_collected_port.connect(coverage.analysis_export);
        end
    endfunction: connect_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("CLKNRST AGENT", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

endclass: clknrst_agent
