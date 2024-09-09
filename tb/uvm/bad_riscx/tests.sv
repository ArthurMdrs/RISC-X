class riscx_base_test extends uvm_test;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    `uvm_component_utils(riscx_base_test)

    clknrst_vif vif_clknrst;
    bad_uvc_vif instr_bad_uvc_vif;
    bad_uvc_vif data_bad_uvc_vif;
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
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "instr_bad_uvc_vif", instr_bad_uvc_vif))
            `uvm_info("BASE TEST", "Virtual interface for Instr bad_uvc was successfully set!", UVM_HIGH)
        else
            `uvm_error("BASE TEST", "No interface for Instr bad_uvc was set!")
        if(uvm_config_db#(bad_uvc_vif)::get(this, "", "data_bad_uvc_vif", data_bad_uvc_vif))
            `uvm_info("BASE TEST", "Virtual interface for Data bad_uvc was successfully set!", UVM_HIGH)
        else
            `uvm_error("BASE TEST", "No interface for Data bad_uvc was set!")
        if(uvm_config_db#(rvvi_vif)::get(this, "", "vif_rvvi", vif_rvvi))
            `uvm_info("BASE TEST", "Virtual interface for RVVI was successfully set!", UVM_HIGH)
        else
            `uvm_error("BASE TEST", "No interface for RVVI was set!")
        
        uvm_config_db#(clknrst_vif)::set(this, "riscx_env_inst", "vif_clknrst"      , vif_clknrst      );
        uvm_config_db#(bad_uvc_vif)::set(this, "riscx_env_inst", "instr_bad_uvc_vif", instr_bad_uvc_vif);
        uvm_config_db#(bad_uvc_vif)::set(this, "riscx_env_inst", "data_bad_uvc_vif" , data_bad_uvc_vif );
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

endclass: riscx_base_test

//==============================================================//

class random_test extends riscx_base_test;

    `uvm_component_utils(random_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        // set_type_override_by_type (bad_uvc_tr#(.XLEN(XLEN),.ALEN(ALEN))::get_type(), bad_uvc_no_wait_tr::get_type());
        
        super.build_phase(phase);

        // Random sequences config - begin
        uvm_config_wrapper::set(this, "riscx_env_inst.vsequencer.run_phase", "default_sequence", riscx_random_vseq::get_type());
        // Random sequences config - end
        
    endfunction: build_phase

endclass: random_test

//==============================================================//

class riscx_dv_test extends riscx_base_test;

    `uvm_component_utils(riscx_dv_test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        uvm_config_wrapper::set(this, "riscx_env_inst.vsequencer.run_phase", "default_sequence", riscx_dv_vseq::get_type());
    endfunction: build_phase

endclass: riscx_dv_test

//==============================================================//

