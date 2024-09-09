class riscx_vseqr #(
    parameter int ILEN   = 32  // Instruction length in bits
) extends uvm_sequencer;

    // bad_uvc_cfg   cfg;
    // bad_uvc_cntxt cntxt;

    `uvm_component_utils_begin(riscx_vseqr)
        // `uvm_field_object(cfg  , UVM_DEFAULT)
        // `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end
    
    clknrst_sqr  sequencer_clknrst;
    bad_uvc_seqr instr_bad_uvc_seqr;
    bad_uvc_seqr data_bad_uvc_seqr;
    
    typedef riscx_vseqr this_type;
    uvm_analysis_imp #(bit [ILEN-1:0], this_type) detected_insn_imp;
    
    bit rvvi_instr_detected = 0;
    bit should_drop_objection = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        detected_insn_imp  = new("detected_insn_imp" , this);
    endfunction: new

    // function void build_phase (uvm_phase phase);
    //     super.build_phase(phase);
    //     void'(uvm_config_db#(bad_uvc_cfg)::get(this, "", "cfg", cfg));
    //     if (cfg == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Config handle is null.")
    //     end      
    //     void'(uvm_config_db#(bad_uvc_cntxt)::get(this, "", "cntxt", cntxt));
    //     if (cntxt == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Context handle is null.")
    //     end      
    // endfunction: build_phase
    
    virtual function void write (bit [ILEN-1:0] t);
        rvvi_instr_detected = 1;
        should_drop_objection = 1;
        `uvm_info("RISC-X VSEQUENCER", $sformatf("Detected instruction 0x%h.", t), UVM_MEDIUM)
    endfunction : write

endclass: riscx_vseqr