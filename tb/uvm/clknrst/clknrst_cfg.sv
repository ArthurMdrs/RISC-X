class clknrst_cfg extends uvm_object;

    uvm_active_passive_enum is_active;
    clknrst_cov_enable_enum cov_control;
    
    rand clknrst_init_val_enum initial_rst_val;

    `uvm_object_utils_begin(clknrst_cfg)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(clknrst_cov_enable_enum, cov_control, UVM_ALL_ON)
        `uvm_field_enum(clknrst_init_val_enum, initial_rst_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new (string name = "clknrst_cfg");
        super.new(name);
        is_active = UVM_ACTIVE;
        cov_control = CLKNRST_COV_ENABLE;
        initial_rst_val = CLKNRST_INITIAL_VALUE_1;
    endfunction: new

endclass: clknrst_cfg
