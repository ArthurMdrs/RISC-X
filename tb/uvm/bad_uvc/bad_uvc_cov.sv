class bad_uvc_cov #(int XLEN=32, int ALEN=32) extends uvm_subscriber #(bad_uvc_tr#(.XLEN(XLEN),.ALEN(ALEN)));

    bad_uvc_cfg   cfg;
    bad_uvc_cntxt cntxt;

    real cov_val;
    bad_uvc_tr cov_transaction;

    `uvm_component_utils_begin(bad_uvc_cov)
        `uvm_field_object(cfg  , UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_object(cntxt, UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_real(cov_val, UVM_ALL_ON)
    `uvm_component_utils_end

    covergroup bad_uvc_covergroup;
        option.per_instance = 1;
        option.name = {get_full_name(), ".", "covergroup"};
        // option.at_least = 3;
        // option.auto_bin_max = 256;
        // option.cross_auto_bin_max = 256;
        cp_addr: coverpoint cov_transaction.addr;
        cp_we: coverpoint cov_transaction.we;
        cp_be: coverpoint cov_transaction.be;
        cp_wdata: coverpoint cov_transaction.wdata;
        cp_rdata: coverpoint cov_transaction.rdata;
    endgroup : bad_uvc_covergroup

    function new (string name, uvm_component parent);
        super.new(name, parent);
        bad_uvc_covergroup = new();
    endfunction: new

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        void'(uvm_config_db#(bad_uvc_cfg)::get(this, "", "cfg", cfg));
        if (cfg == null) begin
            `uvm_fatal("BAD_UVC SEQUENCER", "Config handle is null.")
        end      
        void'(uvm_config_db#(bad_uvc_cntxt)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("BAD_UVC SEQUENCER", "Context handle is null.")
        end      
    endfunction: build_phase

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("BAD_UVC COVERAGE", $sformatf("Coverage: %2.2f%%", get_coverage()), UVM_NONE)
    endfunction : report_phase

    function void sample (bad_uvc_tr t);
        cov_transaction = t;
        bad_uvc_covergroup.sample();
    endfunction : sample

    function real get_coverage ();
        return bad_uvc_covergroup.get_inst_coverage();
    endfunction : get_coverage

    function void write(bad_uvc_tr t);      
        sample(t); // sample coverage with this transaction
        cov_val = get_coverage();
    endfunction : write

endclass : bad_uvc_cov
