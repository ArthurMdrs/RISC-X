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

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
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
