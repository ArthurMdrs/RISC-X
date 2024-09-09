class clknrst_mon extends uvm_monitor;

    clknrst_cfg cfg;

    `uvm_component_utils_begin(clknrst_mon)
        `uvm_field_object(cfg, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end

    clknrst_vif vif;
    clknrst_tr tr;
    int num_tr_col;

    uvm_analysis_port #(clknrst_tr) item_collected_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
            
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST MONITOR", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("CLKNRST MONITOR", "No configuration object was set!")
        
        if(uvm_config_db#(clknrst_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("CLKNRST MONITOR", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("CLKNRST MONITOR", "No interface was set!")
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        // What should we do here?
        forever begin
            // tr = clknrst_tr::type_id::create("tr", this);
            // void'(begin_tr(tr, "CLKNRST_MONITOR_TR"));
            
            vif.wait_clk_posedge();

            // end_tr(tr);
            // item_collected_port.write(tr);
            // num_tr_col++;
        end
    endtask : run_phase

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("CLKNRST MONITOR", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    // function void report_phase(uvm_phase phase);
    //     `uvm_info("CLKNRST MONITOR", $sformatf("Report: CLKNRST MONITOR collected %0d transactions", num_tr_col), UVM_LOW)
    // endfunction : report_phase

endclass: clknrst_mon
