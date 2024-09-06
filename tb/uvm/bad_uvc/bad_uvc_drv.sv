class bad_uvc_drv #(int XLEN=32, int ALEN=32) extends uvm_driver #(bad_uvc_tr#(.XLEN(XLEN),.ALEN(ALEN)));

    bad_uvc_cfg   cfg;
    bad_uvc_cntxt cntxt;

    `uvm_component_utils_begin(bad_uvc_drv)
        `uvm_field_object(cfg  , UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_object(cntxt, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end

    bad_uvc_vif vif;
    int num_sent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_sent = 0;
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "vif", vif))
            `uvm_info("BAD_UVC DRIVER", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("BAD_UVC DRIVER", "No interface was set!")
        
        void'(uvm_config_db#(bad_uvc_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("BAD_UVC DRIVER", "Config handle is null.")
        end      
        void'(uvm_config_db#(bad_uvc_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("BAD_UVC DRIVER", "Context handle is null.")
        end      
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        forever begin : resp_ch
            case (cntxt.rst_state)
                BAD_UVC_RST_STATE_PRE_RESET : vif.wait_clk_negedge();
                BAD_UVC_RST_STATE_IN_RESET  : resp_ch_reset_sigs();
                BAD_UVC_RST_STATE_POST_RESET: resp_ch_post_reset_drv();
            endcase
        end : resp_ch
    endtask: run_phase

    task resp_ch_post_reset_drv();
        seq_item_port.get_next_item(req);
        // `uvm_info("BAD_UVC DRIVER", $sformatf("Driving\n%s", req.sprint()), UVM_NONE)
        void'(begin_tr(req, "BAD_UVC_DRIVER_TR"));
        vif.resp_ch_drive_tr(req);
        seq_item_port.item_done();
        end_tr(req); 
        num_sent++;
    endtask : resp_ch_post_reset_drv

    task resp_ch_reset_sigs();
        vif.resp_ch_reset_sigs();
        // `uvm_info("BAD_UVC DRIVER", "During reset assertion", UVM_NONE)
        vif.wait_clk_negedge();
        // `uvm_info("BAD_UVC DRIVER", "1 negedge clock after reset de-assertion", UVM_NONE)
    endtask : resp_ch_reset_sigs

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("BAD_UVC DRIVER", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("BAD_UVC DRIVER", $sformatf("Report: BAD_UVC DRIVER sent %0d transactions", num_sent), UVM_LOW)
    endfunction : report_phase

endclass: bad_uvc_drv
