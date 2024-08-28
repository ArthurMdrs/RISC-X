class obi_drv #(int XLEN=32, int ALEN=32) extends uvm_driver #(obi_tr#(.XLEN(XLEN),.ALEN(ALEN)));

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_component_utils_begin(obi_drv)
        `uvm_field_object(cfg  , UVM_DEFAULT)
        `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    obi_vif vif;
    int num_sent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_sent = 0;
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", vif))
            `uvm_info("OBI DRIVER", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_error("OBI DRIVER", "No interface was set!")
        
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
        
        fork
            forever begin : addr_ch
                case (cntxt.rst_state)
                    OBI_RST_STATE_PRE_RESET : vif.wait_clk();
                    OBI_RST_STATE_IN_RESET  : addr_ch_reset_sigs();
                    OBI_RST_STATE_POST_RESET: addr_ch_post_reset_drv();
                endcase
            end : addr_ch
            
            forever begin : resp_ch
                case (cntxt.rst_state)
                    OBI_RST_STATE_PRE_RESET : vif.wait_clk();
                    OBI_RST_STATE_IN_RESET  : resp_ch_reset_sigs();
                    OBI_RST_STATE_POST_RESET: resp_ch_post_reset_drv();
                endcase
            end : resp_ch
        join // Is there a reason to make this join_none?
    endtask: run_phase

    task addr_ch_post_reset_drv();
        string msg;
        int unsigned gnt_latency;
        // seq_item_port.get_next_item(req);
        // msg = $sformatf("Driving address channel.\ngnt latency = %0d\nid = %0d", req.gnt_latency, req.id);
        gnt_latency = cfg.get_rnd_gnt_latency();
        msg = $sformatf("Driving address channel. gnt latency = %0d", gnt_latency);
        `uvm_info("OBI DRIVER", msg, UVM_HIGH)
        vif.addr_ch_drive_tr(gnt_latency);
    endtask : addr_ch_post_reset_drv

    task resp_ch_post_reset_drv();
        seq_item_port.get_next_item(req);
        void'(begin_tr(req, "OBI_DRIVER_TR"));
        vif.resp_ch_drive_tr(req);
        seq_item_port.item_done();
        end_tr(req); 
        num_sent++;
    endtask : resp_ch_post_reset_drv

    task addr_ch_reset_sigs();
        vif.addr_ch_reset_sigs();
        vif.wait_clk();
    endtask : addr_ch_reset_sigs

    task resp_ch_reset_sigs();
        vif.resp_ch_reset_sigs();
        vif.wait_clk();
    endtask : resp_ch_reset_sigs

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI DRIVER", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("OBI DRIVER", $sformatf("Report: OBI DRIVER sent %0d transactions", num_sent), UVM_LOW)
    endfunction : report_phase

endclass: obi_drv
