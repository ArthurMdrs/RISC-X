class obi_base_sequence extends uvm_sequence#(obi_tr);

    obi_cfg   cfg;
    obi_cntxt cntxt;

    `uvm_object_utils(obi_base_sequence)
    `uvm_declare_p_sequencer(obi_seqr)

    function new(string name="obi_base_sequence");
        super.new(name);
    endfunction: new

    task pre_start();
        cfg   = p_sequencer.cfg;
        cntxt = p_sequencer.cntxt;
    endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("obi Sequence", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("obi Sequence", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: obi_base_sequence

//==============================================================//

class obi_random_seq extends obi_base_sequence;

    `uvm_object_utils(obi_random_seq)

    function new(string name="obi_random_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        repeat(10) begin
            `uvm_create(req)
                void'(req.randomize());
                // It is possible to put constraints into randomize, like below.
                // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            `uvm_send(req)
        end
    endtask: body

endclass: obi_random_seq

//==============================================================//
