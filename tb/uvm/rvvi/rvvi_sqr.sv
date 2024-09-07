class rvvi_sqr #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_sequencer#(rvvi_tr#(ILEN,XLEN,FLEN));

    rvvi_cfg cfg;

    `uvm_component_param_utils_begin(rvvi_sqr#(ILEN,XLEN,FLEN))
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end
    
    rvvi_vif vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(uvm_config_db#(rvvi_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("RVVI SEQUENCER", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI SEQUENCER", "No configuration object was set!")
        
        if(uvm_config_db#(rvvi_vif)::get(.cntxt(this), .inst_name(""), .field_name("vif"), .value(vif)))
            `uvm_info("RVVI SEQUENCER", "Virtual interface was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI SEQUENCER", "No interface was set!")
    endfunction: build_phase

endclass: rvvi_sqr
