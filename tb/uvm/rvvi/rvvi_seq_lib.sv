class rvvi_base_sequence #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_sequence#(rvvi_tr#(ILEN,XLEN,FLEN));

    rvvi_cfg cfg;

    `uvm_object_utils(rvvi_base_sequence)
    `uvm_declare_p_sequencer(rvvi_sqr#(ILEN,XLEN,FLEN))

    function new(string name="rvvi_base_sequence");
        super.new(name);
    endfunction: new

    task pre_start();
        cfg = p_sequencer.cfg;
    endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("rvvi Sequence", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("rvvi Sequence", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: rvvi_base_sequence

//==============================================================//

class rvvi_random_seq #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends rvvi_base_sequence#(ILEN,XLEN,FLEN);

    `uvm_object_utils(rvvi_random_seq)

    function new(string name="rvvi_random_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("rvvi Sequence", "Executing random sequence.", UVM_LOW)
        repeat(3) begin
            `uvm_create(req)
                void'(req.randomize());
                // It is possible to put constraints into randomize, like below.
                // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            `uvm_send(req)
        end
    endtask: body

endclass: rvvi_random_seq

//==============================================================//
