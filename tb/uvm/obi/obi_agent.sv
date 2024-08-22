class obi_agent #(int XLEN=32, int ALEN=32) extends uvm_agent;

    obi_cfg   cfg;
    obi_cntxt cntxt;

    uvm_active_passive_enum is_active = UVM_ACTIVE;
    obi_cov_enable_enum cov_control = COV_ENABLE;

    `uvm_component_utils_begin(obi_agent)
        `uvm_field_object(cfg  , UVM_DEFAULT)
        `uvm_field_object(cntxt, UVM_DEFAULT)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(obi_cov_enable_enum, cov_control, UVM_ALL_ON)
    `uvm_component_utils_end

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
        
        void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_error("OBI SEQUENCER", "Config handle is null.")
        end      
        void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("OBI SEQUENCER", "Context handle is null.")
        end

        monitor       = obi_mon#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("monitor", this);
        if (is_active == UVM_ACTIVE) begin
            sequencer = obi_seqr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("sequencer", this);
            driver    = obi_drv#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("driver", this);
        end

        if (cov_control == COV_ENABLE) begin
            coverage = obi_cov#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("coverage", this);
            `uvm_info("OBI AGENT", "Coverage is enabled." , UVM_LOW) 
        end else begin
            `uvm_info("OBI AGENT", "Coverage is disabled." , UVM_LOW)
        end
    endfunction: build_phase

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);

        //item_from_monitor_port.connect(monitor.item_collected_port);
        monitor.item_collected_port.connect(item_from_monitor_port);
        
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end

        if (cov_control == COV_ENABLE) begin
            monitor.item_collected_port.connect(coverage.analysis_export);
        end
    endfunction: connect_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI AGENT", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

endclass: obi_agent
