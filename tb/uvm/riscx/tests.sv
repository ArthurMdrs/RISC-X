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
// Design Name:    RISC-X UVM test library                                    //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines UVM tests for RISC-X.                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class base_test extends uvm_test;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    `uvm_component_utils(base_test)

    clknrst_vif vif_clknrst;
    obi_vif instr_obi_vif;
    rvvi_vif    vif_rvvi;
    
    riscx_env riscx_env_inst;

    uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(clknrst_vif)::get(this, "", "vif_clknrst", vif_clknrst))
            `uvm_info("BASE TEST", "Virtual interface for clknrst was successfully set!", UVM_HIGH)
        else
            `uvm_error("BASE TEST", "No interface for clknrst was set!")
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", instr_obi_vif))
            `uvm_info("BASE TEST", "Virtual interface for Instr OBI was successfully set!", UVM_MEDIUM)
        else
            `uvm_error("BASE TEST", "No interface for Instr OBI was set!")
        if(uvm_config_db#(rvvi_vif)::get(this, "", "vif_rvvi", vif_rvvi))
            `uvm_info("BASE TEST", "Virtual interface for RVVI was successfully set!", UVM_HIGH)
        else
            `uvm_error("BASE TEST", "No interface for RVVI was set!")
        
        uvm_config_db#(clknrst_vif)::set(this, "riscx_env_inst", "vif_clknrst"      , vif_clknrst      );
        uvm_config_db#(obi_vif)::set(this, "riscx_env_inst", "instr_obi_vif", instr_obi_vif);
        uvm_config_db#(rvvi_vif   )::set(this, "riscx_env_inst", "vif_rvvi"         , vif_rvvi         );
        
        riscx_env_inst = riscx_env::type_id::create("riscx_env_inst", this);

        `uvm_info("BASE TEST", "Build phase running", UVM_HIGH)
        uvm_config_db#(int)::set(this, "*", "recording_detail", 1);
    endfunction

    function void end_of_elaboration_phase (uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction

    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        check_config_usage();
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        obj = phase.get_objection();
        obj.set_drain_time(this, 200ns);
    endtask: run_phase

endclass: base_test

//==============================================================//

class random_test extends base_test;

    `uvm_component_utils(random_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        set_type_override_by_type (obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::get_type(), obi_no_wait_tr::get_type());
        
        super.build_phase(phase);

        // Sequences config - begin
        uvm_config_wrapper::set(this, "riscx_env_inst.instr_obi_agent.sequencer.run_phase", "default_sequence", obi_random_seq::get_type());
        // Sequences config - end
        
    endfunction: build_phase

endclass: random_test

//==============================================================//

class vseqr_test extends base_test;

    `uvm_component_utils(vseqr_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        // set_type_override_by_type (obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::get_type(), obi_no_wait_tr::get_type());
        
        super.build_phase(phase);

        // Random sequences config - begin
        uvm_config_wrapper::set(this, "riscx_env_inst.vsequencer.run_phase", "default_sequence", riscx_random_vseq::get_type());
        // Random sequences config - end
        
    endfunction: build_phase

    // virtual task run_phase(uvm_phase phase);
    //     super.run_phase(phase);
        
    //     // instr_obi_cntxt.mem.write(32'h8000_0000, 8'h4b);
    //     // instr_obi_cntxt.mem.write(32'h8000_0001, 8'h3a);
    //     // instr_obi_cntxt.mem.write(32'h8000_0002, 8'h29);
    //     // instr_obi_cntxt.mem.write(32'h8000_0003, 8'h18);
    //     // instr_obi_cntxt.mem.write(32'h8000_0b9e, 8'hff);
    //     `uvm_info("BASE TEST", $sformatf("Loading memory.\nBin file: %s", riscx_env_inst.instr_obi_cfg.mem_bin_file), UVM_MEDIUM)
    //     riscx_env_inst.instr_obi_cntxt.mem.load_memory(riscx_env_inst.instr_obi_cfg.mem_bin_file, riscx_env_inst.instr_obi_cfg.mem_start_addr);
    //     riscx_env_inst.instr_obi_cntxt.mem.print_mem();
    // endtask: run_phase

endclass: vseqr_test

//==============================================================//

