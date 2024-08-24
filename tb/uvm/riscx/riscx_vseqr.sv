class riscx_vseqr #(int XLEN=32, int ALEN=32) extends uvm_sequencer#(obi_tr);

    // obi_cfg   cfg;
    // obi_cntxt cntxt;

    `uvm_component_utils_begin(riscx_vseqr)
        // `uvm_field_object(cfg  , UVM_DEFAULT)
        // `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end
    
    obi_seqr instr_obi_seqr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    // function void build_phase (uvm_phase phase);
    //     super.build_phase(phase);
    //     void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
    //     if (cfg == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Config handle is null.")
    //     end      
    //     void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
    //     if (cntxt == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Context handle is null.")
    //     end      
    // endfunction: build_phase

endclass: riscx_vseqr