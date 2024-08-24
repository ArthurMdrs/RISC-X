class riscx_base_vseq extends uvm_sequence;

    // obi_cfg   cfg;
    // obi_cntxt cntxt;

    `uvm_object_utils(riscx_base_vseq)
    `uvm_declare_p_sequencer(riscx_vseqr)

    function new(string name="riscx_base_vseq");
        super.new(name);
    endfunction: new

    // task pre_start();
    //     cfg   = p_sequencer.cfg;
    //     cntxt = p_sequencer.cntxt;
    // endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("RISC-X Sequence", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("RISC-X Sequence", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: riscx_base_vseq

//==============================================================//

class riscx_random_vseq extends riscx_base_vseq;

    `uvm_object_utils(riscx_random_vseq)
    
    obi_random_seq obi_seq1;

    function new(string name="riscx_random_vseq");
        super.new(name);
    endfunction: new
    
    // If a sequence is called via a `uvm_do variant, then it is defined as a 
    // subsequence and it's pre/post_body() methods are not executed
    virtual task body();
        `uvm_do_on(obi_seq1, p_sequencer.instr_obi_seqr);
    endtask: body

endclass: riscx_random_vseq