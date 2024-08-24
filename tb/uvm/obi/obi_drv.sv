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

    // virtual task run_phase (uvm_phase phase);
    //     super.run_phase(phase);
    //     fork
    //         get_and_drive();
    //         reset_signals();
    //     join
    // endtask: run_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        forever begin
            bit tr_started = 0;
            if (cntxt.rst_state == OBI_RST_STATE_POST_RESET) begin
                seq_item_port.get_next_item(req);
                `uvm_info("OBI DRIVER", $sformatf("Sending transaction:\n%s", req.sprint()), UVM_HIGH)
                tr_started = 1;
                void'(begin_tr(req, "OBI_DRIVER_Tr"));
            end
        
            fork
                begin : addr_ch
                    case (cntxt.rst_state)
                        OBI_RST_STATE_PRE_RESET : @(posedge vif.clk);
                        OBI_RST_STATE_IN_RESET  : @(posedge vif.clk);
                        OBI_RST_STATE_POST_RESET: addr_ch_post_reset_drv(req);
                    endcase
                end : addr_ch
                
                begin : resp_ch
                    case (cntxt.rst_state)
                        OBI_RST_STATE_PRE_RESET : @(posedge vif.clk);
                        OBI_RST_STATE_IN_RESET  : @(posedge vif.clk);
                        OBI_RST_STATE_POST_RESET: resp_ch_post_reset_drv(req);
                    endcase
                end : resp_ch
            join // Is there a reason to make this join_none?
            
            if (tr_started) begin
                seq_item_port.item_done();
                end_tr(req); 
            end
        end
    endtask: run_phase

    task addr_ch_post_reset_drv(obi_tr tr);
        // int wait_gnt_cycles;
        // wait_gnt_cycles = tr.wait_gnt_cycles;
        // vif.gnt = 1'b0;
        // // repeat (tr.wait_gnt_cycles) begin
        // //     @(posedge vif.clk);
        // // end
        // while(!)
        // vif.gnt = 1'b1;
        // @(posedge vif.clk);
        vif.addr_ch_drive_tr(tr);
    endtask : addr_ch_post_reset_drv

    task resp_ch_post_reset_drv(obi_tr tr);
        vif.resp_ch_drive_tr(tr);
    endtask : resp_ch_post_reset_drv

    task get_and_drive();
        @(negedge vif.rst_n);
        @(posedge vif.rst_n);

        `uvm_info("OBI DRIVER", "Reset dropped", UVM_MEDIUM)

        forever begin
            // Get new item from the sequencer
            seq_item_port.get_next_item(req);
            `uvm_info("OBI DRIVER", $sformatf("Sending transaction:%s", req.convert2string()), UVM_MEDIUM)

            // concurrent blocks for transaction driving and transaction recording
            fork
                // send transaction
                begin
                    // send transaction via interface
                    vif.send_to_dut(req);
                end

                // Start transaction recording at start of transaction (vif.drvstart triggered from interface.send_to_dut())
                begin
                    @(posedge vif.drvstart) void'(begin_tr(req, "OBI_DRIVER_Tr"));
                end
            join

            end_tr(req);
            num_sent++;
            seq_item_port.item_done();
        end
    endtask : get_and_drive

    // task reset_signals();
    //     forever begin
    //         vif.obi_reset();
    //         `uvm_info("OBI DRIVER", "Reset done", UVM_NONE)
    //     end
    // endtask : reset_signals

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("OBI DRIVER", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("OBI DRIVER", $sformatf("Report: OBI DRIVER sent %0d transactions", num_sent), UVM_LOW)
    endfunction : report_phase

endclass: obi_drv
