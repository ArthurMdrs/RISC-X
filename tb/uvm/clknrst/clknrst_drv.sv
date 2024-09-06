class clknrst_drv extends uvm_driver #(clknrst_tr);

    clknrst_cfg cfg;

    `uvm_component_utils_begin(clknrst_drv)
        `uvm_field_object(cfg, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end

    clknrst_vif vif;
    int num_sent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_sent = 0;
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
            
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST DRIVER", "Configuration object was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST DRIVER", "No configuration object was set!")
        
        if(uvm_config_db#(clknrst_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("CLKNRST DRIVER", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST DRIVER", "No interface was set!")
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        
        case (cfg.initial_rst_val)
            CLKNRST_INITIAL_VALUE_0: vif.set_rst_val(1'b0);
            CLKNRST_INITIAL_VALUE_1: vif.set_rst_val(1'b1);
            CLKNRST_INITIAL_VALUE_X: vif.set_rst_val(1'bx);
            default: `uvm_fatal("CLKNRST DRIVER", $sformatf("Illegal initial value for reset: %s", cfg.initial_rst_val))
        endcase

        forever begin
            seq_item_port.get_next_item(req);
            void'(begin_tr(req, "CLKNRST_DRIVER_TR"));
            drive_req (req);
            end_tr(req);
            num_sent++;
            seq_item_port.item_done();
        end
    endtask: run_phase



    task drive_req(clknrst_tr req);
        case (req.action)
            CLKNRST_ACTION_START_CLK: begin
                if (vif.clk_active) begin
                    `uvm_warning("CLKNRST DRIVER", $sformatf("Attempting to start clock generation while it is already active. Ignoring req:\n%s", req.sprint()))
                end
                else begin
                    if (req.clk_period != 0) begin
                        vif.set_period(req.clk_period * 1ps);
                    end
                    case (req.initial_clk_val)
                        CLKNRST_INITIAL_VALUE_0: vif.set_clk_val(1'b0);
                        CLKNRST_INITIAL_VALUE_1: vif.set_clk_val(1'b1);
                        CLKNRST_INITIAL_VALUE_X: vif.set_clk_val(1'bx);
                    endcase
                    vif.start_clk();
                end
            end
            
            CLKNRST_ACTION_STOP_CLK: begin
                if (!vif.clk_active) begin
                    `uvm_warning("CLKNRST DRIVER", $sformatf("Attempting to stop clock generation while it is already inactive. Ignoring req:\n%s", req.sprint()))
                end
                else begin
                    // wait (vif.clk == 1'b0);
                    vif.stop_clk();
                end
            end
        
            CLKNRST_ACTION_RESTART_CLK: begin
                if (vif.clk_active) begin
                    `uvm_warning("CLKNRST DRIVER", $sformatf("Attempting to restart clock generation while it is already active. Ignoring req:\n%s", req.sprint()))
                end
                else begin
                    vif.start_clk();
                end
            end
        
            CLKNRST_ACTION_ASSERT_RESET: begin
                vif.assert_rst(req.rst_assert_duration);
            end
        endcase
    endtask : drive_req

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("CLKNRST DRIVER", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("CLKNRST DRIVER", $sformatf("Report: CLKNRST DRIVER sent %0d transactions", num_sent), UVM_LOW)
    endfunction : report_phase

endclass: clknrst_drv
