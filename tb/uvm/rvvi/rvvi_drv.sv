// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    RVVI driver                                                //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVVI driver.                                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class rvvi_drv #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_driver #(rvvi_tr#(ILEN,XLEN,FLEN));

    rvvi_cfg cfg;

    `uvm_component_param_utils_begin(rvvi_drv#(ILEN,XLEN,FLEN))
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end

    rvvi_vif vif; // TODO: does this have to be parameterized?
    int num_sent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        num_sent = 0;
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
            
        if(uvm_config_db#(rvvi_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("RVVI DRIVER", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI DRIVER", "No configuration object was set!")
        
        if(uvm_config_db#(rvvi_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("RVVI DRIVER", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI DRIVER", "No interface was set!")
    endfunction: build_phase

    virtual task run_phase (uvm_phase phase);
        super.run_phase(phase);
        fork
            get_and_drive();
            reset_signals();
        join
    endtask: run_phase

    task get_and_drive();
        @(negedge vif.rst_n);
        @(posedge vif.rst_n);

        `uvm_info("RVVI DRIVER", "Reset dropped", UVM_MEDIUM)

        forever begin
            // Get new item from the sequencer
            seq_item_port.get_next_item(req);
            `uvm_info("RVVI DRIVER", $sformatf("Sending transaction:%s", req.convert2string()), UVM_HIGH)

            // concurrent blocks for transaction driving and transaction recording
            fork
                // send transaction
                begin
                    // send transaction via interface
                    vif.send_to_dut(req);
                end

                // Start transaction recording at start of transaction (vif.drvstart triggered from interface.send_to_dut())
                begin
                    @(posedge vif.drvstart) void'(begin_tr(req, "RVVI_DRIVER_TR"));
                end
            join

            end_tr(req);
            num_sent++;
            seq_item_port.item_done();
        end
    endtask : get_and_drive

    task reset_signals();
        forever begin
            vif.rvvi_reset();
            `uvm_info("RVVI DRIVER", "Detected reset", UVM_LOW)
        end
    endtask : reset_signals

    function void start_of_simulation_phase (uvm_phase phase);
        super.start_of_simulation_phase(phase);
        `uvm_info("RVVI DRIVER", "Simulation initialized", UVM_HIGH)
    endfunction: start_of_simulation_phase

    function void report_phase(uvm_phase phase);
        `uvm_info("RVVI DRIVER", $sformatf("Report: RVVI DRIVER sent %0d transactions", num_sent), UVM_NONE)
    endfunction : report_phase

endclass: rvvi_drv
