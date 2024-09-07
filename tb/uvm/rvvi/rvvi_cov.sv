class rvvi_cov #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_subscriber #(rvvi_tr#(ILEN,XLEN,FLEN));

    rvvi_cfg cfg;

    real coverage_value;
    rvvi_tr cov_transaction;

    `uvm_component_param_utils_begin(rvvi_cov#(ILEN,XLEN,FLEN))
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_real(coverage_value, UVM_ALL_ON)
    `uvm_component_utils_end

    covergroup rvvi_covergroup;
        option.per_instance = 1;
        option.name = {get_full_name(), ".", "covergroup"};
        // option.at_least = 3;
        // option.auto_bin_max = 256;
        // option.cross_auto_bin_max = 256;
        cp_order: coverpoint cov_transaction.order;
        cp_insn: coverpoint cov_transaction.insn;
        cp_trap: coverpoint cov_transaction.trap;
        cp_debug_mode: coverpoint cov_transaction.debug_mode;
        cp_pc_rdata: coverpoint cov_transaction.pc_rdata;
        cp_x_wdata: coverpoint cov_transaction.x_wdata;
        cp_x_wb: coverpoint cov_transaction.x_wb;
        cp_f_wdata: coverpoint cov_transaction.f_wdata;
        cp_f_wb: coverpoint cov_transaction.f_wb;
        // cp_v_wdata: coverpoint cov_transaction.v_wdata;
        // cp_v_wb: coverpoint cov_transaction.v_wb;
        cp_csr: coverpoint cov_transaction.csr;
        cp_csr_wb: coverpoint cov_transaction.csr_wb;
        // cp_lrsc_cancel: coverpoint cov_transaction.lrsc_cancel;
        cp_pc_wdata: coverpoint cov_transaction.pc_wdata;
        cp_intr: coverpoint cov_transaction.intr;
        cp_halt: coverpoint cov_transaction.halt;
        cp_ixl: coverpoint cov_transaction.ixl;
        cp_mode: coverpoint cov_transaction.mode;
    endgroup : rvvi_covergroup

    function new (string name, uvm_component parent);
        super.new(name, parent);
        rvvi_covergroup = new();
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if(uvm_config_db#(rvvi_cfg)::get(.cntxt(this), .inst_name(""), .field_name("cfg"), .value(cfg)))
            `uvm_info("RVVI COVERAGE", "Configuration object was successfully set!", UVM_HIGH)
        else
            `uvm_fatal("RVVI COVERAGE", "No configuration object was set!")
    endfunction: build_phase

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("RVVI COVERAGE", $sformatf("Coverage: %2.2f%%", get_coverage()), UVM_NONE)
    endfunction : report_phase

    function void sample (rvvi_tr t);
        cov_transaction = t;
        rvvi_covergroup.sample();
    endfunction : sample

    function real get_coverage ();
        return rvvi_covergroup.get_inst_coverage();
    endfunction : get_coverage

    function void write(rvvi_tr t);      
        sample(t); // sample coverage with this transaction
        coverage_value = get_coverage();
    endfunction : write

endclass : rvvi_cov
