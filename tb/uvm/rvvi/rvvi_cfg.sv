class rvvi_cfg #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_object;

    uvm_active_passive_enum  is_active;
    rvvi_cov_enable_enum     cov_control;
    rvvi_logging_enable_enum log_control;
    
    // If detect_insn = 1, the monitor will check if detect_insn_val shows up in the interface
    // Can be used to catch ecall and detect the end of a test
    bit            detect_insn;
    bit [ILEN-1:0] detect_insn_val;

    `uvm_object_param_utils_begin(rvvi_cfg#(ILEN,XLEN,FLEN))
        `uvm_field_enum(uvm_active_passive_enum , is_active      , UVM_ALL_ON)
        `uvm_field_enum(rvvi_cov_enable_enum    , cov_control    , UVM_ALL_ON)
        `uvm_field_enum(rvvi_logging_enable_enum, log_control    , UVM_ALL_ON)
        `uvm_field_int (                          detect_insn    , UVM_ALL_ON)
        `uvm_field_int (                          detect_insn_val, UVM_ALL_ON)
    `uvm_object_utils_end

    function new (string name = "rvvi_cfg");
        super.new(name);
        
        is_active = UVM_ACTIVE;
        cov_control = RVVI_COV_ENABLE;
        log_control = RVVI_LOGGING_ENABLE;
        
        detect_insn = 0;
        detect_insn_val = '0;
    endfunction: new

endclass: rvvi_cfg
