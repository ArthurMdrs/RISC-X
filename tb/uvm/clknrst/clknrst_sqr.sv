class clknrst_sqr extends uvm_sequencer#(clknrst_tr);

    clknrst_cfg cfg;

    `uvm_component_utils_begin(clknrst_sqr)
        `uvm_field_object(cfg, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end
    
    clknrst_vif vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(clknrst_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("CLKNRST SEQUENCER", "Configuration object was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST SEQUENCER", "No configuration object was set!")
        
        if(uvm_config_db#(clknrst_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("CLKNRST SEQUENCER", "Virtual interface was successfully set!", UVM_MEDIUM)
        else
            `uvm_fatal("CLKNRST SEQUENCER", "No interface was set!")
    endfunction: build_phase

endclass: clknrst_sqr
