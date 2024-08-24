class base_test extends uvm_test;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    `uvm_component_utils(base_test)

    obi_vif instr_obi_vif;
    
    riscx_env riscx_env_inst;

    uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(obi_vif)::get(this, "", "vif", instr_obi_vif))
            `uvm_info("BASE TEST", "Virtual interface for Instr OBI was successfully set!", UVM_MEDIUM)
        else
            `uvm_error("BASE TEST", "No interface for Instr OBI was set!")
        
        uvm_config_db#(obi_vif)::set(this, "riscx_env_inst", "instr_obi_vif", instr_obi_vif);
        
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
        set_type_override_by_type (obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::get_type(), obi_no_wait_tr::get_type());
        
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
    //     // instr_obi_cntxt.mem.load_memory("/home/pedro.medeiros/Tools/RISC-X/tb/uvm/riscx_env/riscv_arithmetic_basic_test_0.bin");
        
    //     instr_obi_cntxt.mem.print_mem();
    // endtask: run_phase

endclass: vseqr_test

//==============================================================//

