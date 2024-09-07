class rvvi_agent #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_agent;

    rvvi_cfg cfg; // TODO: does this have to be parameterized?

    `uvm_component_param_utils_begin(rvvi_agent#(ILEN,XLEN,FLEN))
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end

    rvvi_vif    vif;
    rvvi_mon    monitor;
    rvvi_drv    driver;
    rvvi_sqr    sequencer;
    rvvi_cov    coverage;
    rvvi_tr_log tr_logger;

    uvm_analysis_port #(rvvi_tr#(ILEN,XLEN,FLEN)) item_from_monitor_port;

    function new (string name, uvm_component parent);
        super.new(name, parent);
        item_from_monitor_port = new("item_from_monitor_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(rvvi_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("RVVI AGENT", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI AGENT", "No configuration object was set!")
        uvm_config_db#(rvvi_cfg)::set(.cntxt(this), .inst_name("*"), .field_name("cfg"), .value(cfg));
        
        if(uvm_config_db#(rvvi_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("RVVI AGENT", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI AGENT", "No interface was set!")
        uvm_config_db#(rvvi_vif)::set(.cntxt(this), .inst_name("*"), .field_name("vif"), .value(vif));
        
        monitor       = rvvi_mon#(ILEN,XLEN,FLEN)::type_id::create("monitor", this);
        if (cfg.is_active == UVM_ACTIVE) begin
            sequencer = rvvi_sqr#(ILEN,XLEN,FLEN)::type_id::create("sequencer", this);
            driver    = rvvi_drv#(ILEN,XLEN,FLEN)::type_id::create("driver", this);
            `uvm_info("RVVI AGENT", "Agent is active." , UVM_MEDIUM)
        end else begin
            `uvm_info("RVVI AGENT", "Agent is not active." , UVM_MEDIUM)
        end

        if (cfg.cov_control == RVVI_COV_ENABLE) begin
            coverage = rvvi_cov#(ILEN,XLEN,FLEN)::type_id::create("coverage", this);
            `uvm_info("RVVI AGENT", "Coverage is enabled." , UVM_MEDIUM)
        end else begin
            `uvm_info("RVVI AGENT", "Coverage is disabled." , UVM_MEDIUM)
        end

        if (cfg.log_control == RVVI_LOGGING_ENABLE) begin
            tr_logger = rvvi_tr_log#(ILEN,XLEN,FLEN)::type_id::create("tr_logger", this);
            `uvm_info("RVVI AGENT", "Logging is enabled." , UVM_MEDIUM)
        end else begin
            `uvm_info("RVVI AGENT", "Logging is disabled." , UVM_MEDIUM)
        end
    endfunction: build_phase

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);

        monitor.item_collected_port.connect(item_from_monitor_port);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end

        if (cfg.cov_control == RVVI_COV_ENABLE) begin
            monitor.item_collected_port.connect(coverage.analysis_export);
        end

        if (cfg.log_control == RVVI_LOGGING_ENABLE) begin
            monitor.item_collected_port.connect(tr_logger.analysis_export);
        end
    endfunction: connect_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("RVVI AGENT", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

endclass: rvvi_agent
