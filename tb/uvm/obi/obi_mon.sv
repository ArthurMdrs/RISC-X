class obi_mon #(int XLEN=32, int ALEN=32) extends uvm_monitor;

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_component_param_utils_begin(obi_mon#(XLEN, ALEN))
        `uvm_field_object(cfg  , UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_object(cntxt, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end

    obi_vif vif;
    int num_tr_col;

    uvm_analysis_port #(obi_tr#(.XLEN(XLEN),.ALEN(ALEN))) item_collected_port;
    uvm_analysis_port #(obi_tr#(.XLEN(XLEN),.ALEN(ALEN))) to_seqr_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_tr_col = 0;
        item_collected_port = new("item_collected_port", this);
        to_seqr_port = new("to_seqr_port", this);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", vif))
            `uvm_info("OBI MONITOR", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("OBI MONITOR", "No interface was set!")   
        
        void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("OBI MONITOR", "Config handle is null.")
        end      
        void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("OBI MONITOR", "Context handle is null.")
        end     
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        fork
            observe_reset();
            
            forever begin : addr_ch
                case (cntxt.rst_state)
                    OBI_RST_STATE_PRE_RESET : vif.wait_clk();
                    OBI_RST_STATE_IN_RESET  : vif.wait_clk();
                    OBI_RST_STATE_POST_RESET: addr_ch_post_reset_mon();
                endcase
            end : addr_ch
        
            forever begin : resp_ch
                case (cntxt.rst_state)
                    OBI_RST_STATE_PRE_RESET : vif.wait_clk();
                    OBI_RST_STATE_IN_RESET  : vif.wait_clk();
                    OBI_RST_STATE_POST_RESET: resp_ch_post_reset_mon();
                endcase
            end : resp_ch
        join // Is there a reason to make this join_none?
    endtask : run_phase

    task observe_reset();
        forever begin
            wait (vif.rst_n === 0);
            cntxt.rst_state = OBI_RST_STATE_IN_RESET;
            `uvm_info("OBI MONITOR", $sformatf("Currently in reset state."), UVM_LOW)
            // vif.addr_ch_reset_sigs();
            // vif.resp_ch_reset_sigs();
            vif.obi_reset_sigs();
            wait (vif.rst_n === 1);
            cntxt.rst_state = OBI_RST_STATE_POST_RESET;
            `uvm_info("OBI MONITOR", $sformatf("Currently in post reset state."), UVM_LOW)
        end
    endtask : observe_reset

    task addr_ch_post_reset_mon();
        obi_tr tr;
        tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);
        void'(begin_tr(tr, "OBI_MON_ADDR_TR"));
        vif.addr_ch_collect_tr(tr);
        `uvm_info("OBI MONITOR", $sformatf("Transaction Collected in Address Channel:\n%s", tr.sprint()), UVM_MEDIUM)
        to_seqr_port.write(tr);
        vif.wait_clk();
        end_tr(tr);
    endtask : addr_ch_post_reset_mon

    task resp_ch_post_reset_mon();
        obi_tr tr;
        tr = obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("tr", this);
        void'(begin_tr(tr, "OBI_MON_RESP_TR"));
        vif.resp_ch_collect_tr(tr);
        vif.wait_clk();
        end_tr(tr);
        num_tr_col++;
        `uvm_info("OBI MONITOR", $sformatf("Transaction Collected in Response Channel:\n%s", tr.sprint()), UVM_MEDIUM)
    endtask : resp_ch_post_reset_mon

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI MONITOR", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("OBI MONITOR", $sformatf("Report: OBI MONITOR collected %0d transactions", num_tr_col), UVM_LOW)
    endfunction : report_phase

endclass: obi_mon
