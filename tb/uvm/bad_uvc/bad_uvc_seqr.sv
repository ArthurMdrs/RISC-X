class bad_uvc_seqr #(int XLEN=32, int ALEN=32) extends uvm_sequencer#(bad_uvc_tr);

    bad_uvc_cfg   cfg;
    bad_uvc_cntxt cntxt;

    `uvm_component_utils_begin(bad_uvc_seqr)
        `uvm_field_object(cfg  , UVM_ALL_ON|UVM_NOPRINT)
        `uvm_field_object(cntxt, UVM_ALL_ON|UVM_NOPRINT)
    `uvm_component_utils_end
    
    uvm_tlm_analysis_fifo #(bad_uvc_tr#(.XLEN(XLEN),.ALEN(ALEN))) mon_tr_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        
        mon_tr_fifo = new("mon_tr_fifo", this);
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

endclass: bad_uvc_seqr
