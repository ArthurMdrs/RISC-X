class rvvi_cfg #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_object;

    uvm_active_passive_enum  is_active;
    rvvi_cov_enable_enum     cov_control;
    rvvi_logging_enable_enum log_control;

    `uvm_object_param_utils_begin(rvvi_cfg#(ILEN,XLEN,FLEN))
        `uvm_field_enum(uvm_active_passive_enum , is_active  , UVM_ALL_ON)
        `uvm_field_enum(rvvi_cov_enable_enum    , cov_control, UVM_ALL_ON)
        `uvm_field_enum(rvvi_logging_enable_enum, log_control, UVM_ALL_ON)
    `uvm_object_utils_end

    function new (string name = "rvvi_cfg");
        super.new(name);
        is_active = UVM_ACTIVE;
        cov_control = RVVI_COV_ENABLE;
        log_control = RVVI_LOGGING_ENABLE;
    endfunction: new

endclass: rvvi_cfg
