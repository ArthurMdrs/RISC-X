class obi_mon #(int XLEN=32, int ALEN=32) extends uvm_monitor;

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_component_utils_begin(obi_mon)
        `uvm_field_object(cfg  , UVM_DEFAULT)
        `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    obi_vif vif;
    // obi_tr tr;
    int num_tr_col;

    uvm_analysis_port #(obi_tr) item_collected_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", vif))
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

    // virtual task run_phase (uvm_phase phase);
    //     super.run_phase(phase);
    //     @(negedge vif.rst_n);
    //     @(posedge vif.rst_n);

    //     `uvm_info("OBI MONITOR", "Reset dropped", UVM_MEDIUM)

    //     forever begin
    //         tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);

    //         // concurrent blocks for transaction collection and transaction recording
    //         fork
    //             // collect transaction
    //             begin
    //                 // collect transaction from interface
    //                 vif.collect_tr(tr);
    //             end

    //             // Start transaction recording at start of transaction (vif.monstart triggered from interface.collect_tr())
    //             begin
    //                 @(posedge vif.monstart) void'(begin_tr(tr, "OBI_MONITOR_Tr"));
    //             end
    //         join

    //         end_tr(tr);
    //         `uvm_info("OBI MONITOR", $sformatf("Transaction Collected:\n%s", tr.convert2string()), UVM_LOW)
    //         item_collected_port.write(tr);
    //         num_tr_col++;
    //     end
    // endtask : run_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        fork
            observe_reset();
            
            begin : addr_ch
                forever begin
                    case (cntxt.rst_state)
                        // OBI_RST_STATE_PRE_RESET : addr_ch_pre_reset ();
                        // OBI_RST_STATE_IN_RESET  : addr_ch_in_reset  ();
                        OBI_RST_STATE_PRE_RESET : @(posedge vif.clk);
                        OBI_RST_STATE_IN_RESET  : @(posedge vif.clk);
                        OBI_RST_STATE_POST_RESET: addr_ch_post_reset_mon();
                    endcase
                end
            end : addr_ch
            
            begin : resp_ch
                forever begin
                    case (cntxt.rst_state)
                        OBI_RST_STATE_PRE_RESET : @(posedge vif.clk);
                        OBI_RST_STATE_IN_RESET  : @(posedge vif.clk);
                        OBI_RST_STATE_POST_RESET: resp_ch_post_reset_mon();
                    endcase
                end
            end : resp_ch
        join // Is there a reason to make this join_none?
    endtask : run_phase

    task observe_reset();
        forever begin
            wait (vif.rst_n === 0);
            cntxt.rst_state = OBI_RST_STATE_IN_RESET;
            `uvm_info("OBI MONITOR", $sformatf("Currently in reset state."), UVM_NONE)
            wait (vif.rst_n === 1);
            cntxt.rst_state = OBI_RST_STATE_POST_RESET;
            `uvm_info("OBI MONITOR", $sformatf("Currently in post reset state."), UVM_NONE)
        end
    endtask : observe_reset

    task addr_ch_post_reset_mon();
        obi_tr tr;
        // `uvm_info("OBI MONITOR", "We are in addr_ch_post_reset_mon", UVM_LOW)
        tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);
        vif.addr_ch_collect_tr(tr);
        // addr_ch_collect_tr(tr);
        `uvm_info("OBI MONITOR", $sformatf("Transaction Collected in Address Channel:\n%s", tr.sprint()), UVM_MEDIUM)
    endtask : addr_ch_post_reset_mon

    task resp_ch_post_reset_mon();
        obi_tr tr;
        // `uvm_info("OBI MONITOR", "We are in resp_ch_post_reset_mon", UVM_LOW)
        // tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);
        vif.resp_ch_collect_tr(tr);
        `uvm_info("OBI MONITOR", $sformatf("Transaction Collected in Response Channel:\n%s", tr.sprint()), UVM_MEDIUM)
    endtask : resp_ch_post_reset_mon

    // task addr_ch_collect_tr(output obi_tr tr);
    //     tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);
        
    //     while (!(vif.req && vif.gnt)) begin
    //         @(posedge vif.clk);
    //     end
        
    //     tr.addr = vif.addr;
    //     tr.we = vif.we;
    //     tr.be = vif.be;
    //     tr.wdata = vif.wdata;
    // endtask : addr_ch_collect_tr

    // task observe_reset();
        
    // endtask : observe_reset

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI MONITOR", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("OBI MONITOR", $sformatf("Report: OBI MONITOR collected %0d transactions", num_tr_col), UVM_LOW)
    endfunction : report_phase

endclass: obi_mon
