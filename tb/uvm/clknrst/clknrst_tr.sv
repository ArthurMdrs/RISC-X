class clknrst_tr extends uvm_sequence_item;
    
    rand clknrst_action_enum   action;
    rand int unsigned          rst_assert_duration;     // In ps
    rand int unsigned          clk_period;              // In ps
    rand clknrst_init_val_enum initial_clk_val;
    
    `uvm_object_utils_begin(clknrst_tr)
        `uvm_field_enum(clknrst_action_enum  , action         , UVM_ALL_ON)
        `uvm_field_int (rst_assert_duration                   , UVM_ALL_ON)
        `uvm_field_int (clk_period                            , UVM_ALL_ON)
        `uvm_field_enum(clknrst_init_val_enum, initial_clk_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="clknrst_tr");
        super.new(name);
    endfunction: new

    constraint max_clk_period {
        clk_period <= 20_000; // 20ns
    }

    constraint max_rst_assert_duration {
        rst_assert_duration <= 15_000; // 15ns
    }

endclass: clknrst_tr
