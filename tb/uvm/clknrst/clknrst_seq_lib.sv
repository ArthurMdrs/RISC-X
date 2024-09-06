class clknrst_base_sequence extends uvm_sequence#(clknrst_tr);

    clknrst_cfg cfg;

    `uvm_object_utils(clknrst_base_sequence)
    `uvm_declare_p_sequencer(clknrst_sqr)

    function new(string name="clknrst_base_sequence");
        super.new(name);
    endfunction: new

    task pre_start();
        cfg = p_sequencer.cfg;
    endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("clknrst Sequence", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("clknrst Sequence", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: clknrst_base_sequence

//==============================================================//

class clknrst_start_clk_seq extends clknrst_base_sequence;

    `uvm_object_utils(clknrst_start_clk_seq)

    function new(string name="clknrst_start_clk_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("clknrst Sequence", "Executing start_clk sequence.", UVM_LOW)
        `uvm_create(req)
        if (!req.randomize())
            `uvm_fatal("clknrst start_clk_seq", "Failed randomizing sequence item.")
        req.action = CLKNRST_ACTION_START_CLK;
        `uvm_send(req)
    endtask: body

endclass: clknrst_start_clk_seq

//==============================================================//

class clknrst_stop_clk_seq extends clknrst_base_sequence;

    `uvm_object_utils(clknrst_stop_clk_seq)

    function new(string name="clknrst_stop_clk_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("clknrst Sequence", "Executing stop_clk sequence.", UVM_LOW)
        `uvm_create(req)
        if (!req.randomize())
            `uvm_fatal("clknrst stop_clk_seq", "Failed randomizing sequence item.")
        req.action = CLKNRST_ACTION_STOP_CLK;
        `uvm_send(req)
    endtask: body

endclass: clknrst_stop_clk_seq

//==============================================================//

class clknrst_restart_clk_seq extends clknrst_base_sequence;

    `uvm_object_utils(clknrst_restart_clk_seq)

    function new(string name="clknrst_restart_clk_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("clknrst Sequence", "Executing restart_clk sequence.", UVM_LOW)
        `uvm_create(req)
        if (!req.randomize())
            `uvm_fatal("clknrst restart_clk_seq", "Failed randomizing sequence item.")
        req.action = CLKNRST_ACTION_RESTART_CLK;
        `uvm_send(req)
    endtask: body

endclass: clknrst_restart_clk_seq

//==============================================================//

class clknrst_assert_reset_seq extends clknrst_base_sequence;

    `uvm_object_utils(clknrst_assert_reset_seq)

    function new(string name="clknrst_assert_reset_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("clknrst Sequence", "Executing assert_reset sequence.", UVM_LOW)
        `uvm_create(req)
        if (!req.randomize())
            `uvm_fatal("clknrst assert_reset_seq", "Failed randomizing sequence item.")
        req.action = CLKNRST_ACTION_ASSERT_RESET;
        `uvm_send(req)
    endtask: body

endclass: clknrst_assert_reset_seq

//==============================================================//

class clknrst_reset_and_start_clk_seq extends clknrst_base_sequence;
    
    clknrst_start_clk_seq    start_clk_seq;
    clknrst_assert_reset_seq assert_reset_seq;
    
    `uvm_object_utils(clknrst_reset_and_start_clk_seq)

    function new(string name="clknrst_reset_and_start_clk_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("clknrst Sequence", "Executing reset_and_start_clk sequence.", UVM_LOW)
        `uvm_do(start_clk_seq)
        // p_sequencer.vif.wait_clk_posedge();
        p_sequencer.vif.wait_clk_negedge();
        `uvm_do(assert_reset_seq)
    endtask: body

endclass: clknrst_reset_and_start_clk_seq

//==============================================================//
