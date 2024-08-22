class obi_mon #(int XLEN=32, int ALEN=32) extends uvm_monitor;

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_component_utils_begin(obi_mon)
        `uvm_field_object(cfg  , UVM_DEFAULT)
        `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    obi_vif vif;
    obi_tr tr;
    int num_tr_col;

    uvm_analysis_port #(obi_tr) item_collected_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(obi_vif_config::get(this, "", "vif", vif))
            `uvm_info("OBI MONITOR", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_error("OBI MONITOR", "No interface was set!")   
        
        void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("OBI SEQUENCER", "Config handle is null.")
        end      
        void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("OBI SEQUENCER", "Context handle is null.")
        end     
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        @(negedge vif.rst_n);
        @(posedge vif.rst_n);

        `uvm_info("OBI MONITOR", "Reset dropped", UVM_MEDIUM)

        forever begin
            tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);

            // concurrent blocks for transaction collection and transaction recording
            fork
                // collect transaction
                begin
                    // collect transaction from interface
                    vif.collect_tr(tr);
                end

                // Start transaction recording at start of transaction (vif.monstart triggered from interface.collect_tr())
                begin
                    @(posedge vif.monstart) void'(begin_tr(tr, "OBI_MONITOR_Tr"));
                end
            join

            end_tr(tr);
            `uvm_info("OBI MONITOR", $sformatf("Transaction Collected:\n%s", tr.convert2string()), UVM_LOW)
            item_collected_port.write(tr);
            num_tr_col++;
        end
    endtask : run_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI MONITOR", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("OBI MONITOR", $sformatf("Report: OBI MONITOR collected %0d transactions", num_tr_col), UVM_LOW)
    endfunction : report_phase

endclass: obi_mon
