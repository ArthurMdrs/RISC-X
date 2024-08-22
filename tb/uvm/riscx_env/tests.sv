class base_test extends uvm_test;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    obi_cfg   instr_obi_cfg;
    obi_cntxt instr_obi_cntxt;

    `uvm_component_utils_begin(base_test)
      `uvm_field_object(instr_obi_cfg  , UVM_DEFAULT)
      `uvm_field_object(instr_obi_cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    // VIPs instances - begin
    obi_agent agent_obi;
    // VIPs instances - end

    uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        instr_obi_cfg   = obi_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cfg"  );
        instr_obi_cntxt = obi_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cntxt");
        
        uvm_config_db#(obi_cfg  )::set(this, "agent_obi*", "cfg"  , instr_obi_cfg  );
        uvm_config_db#(obi_cntxt)::set(this, "agent_obi*", "cntxt", instr_obi_cntxt);

        // Edit to set some agent to passive
        // uvm_config_db#(int)::set(this, "some_vip", "is_active", UVM_PASSIVE);

        // Edit to disable some agent's coverage
        // uvm_config_db#(int)::set(this, "some_vip", "cov_control", COV_DISABLE);

        // VIPs creation - begin
        agent_obi = obi_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("agent_obi", this);
        // VIPs creation - end

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
        // Override transaction types, eg:
        //      original_type_name::type_id::set_type_override(override_type_name::get_type());
        //      set_type_override_by_type (some_agent::get_type(), child_agent::get_type());
        //      set_inst_override_by_type ("some_agent.*", some_agent::get_type(), child_agent::get_type());
        set_type_override_by_type (obi_tr#(.XLEN(XLEN),.ALEN(ALEN))::get_type(), obi_no_wait_tr::get_type());
        super.build_phase(phase);

        // Random sequences config - begin
        uvm_config_wrapper::set(this, "agent_obi.sequencer.run_phase", "default_sequence", obi_random_seq::get_type());
        // Random sequences config - end
        
    endfunction: build_phase

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        // instr_obi_cntxt.mem.write(32'h8000_0000, 8'h4b);
        // instr_obi_cntxt.mem.write(32'h8000_0001, 8'h3a);
        // instr_obi_cntxt.mem.write(32'h8000_0002, 8'h29);
        // instr_obi_cntxt.mem.write(32'h8000_0003, 8'h18);
        // instr_obi_cntxt.mem.write(32'h8000_0b9e, 8'hff);
        instr_obi_cntxt.mem.load_memory("/home/xmen/Projects/riscv-formal/cores/risc-x/RISC-X/tb/riscv-dv/mytest/asm_test/riscv_rand_jump_test_0.bin");
        
        instr_obi_cntxt.mem.print_mem();
    endtask: run_phase

endclass: random_test

//==============================================================//
