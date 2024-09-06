package bad_uvc_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "riscx_mem_model.sv"
    
    `include "bad_uvc_tdefs.sv"

    typedef virtual interface bad_uvc_if bad_uvc_vif;

    `include "bad_uvc_cntxt.sv"
    `include "bad_uvc_cfg.sv"
    `include "bad_uvc_tr.sv"
    `include "bad_uvc_seqr.sv"
    `include "bad_uvc_seq_lib.sv"
    `include "bad_uvc_mon.sv"
    `include "bad_uvc_drv.sv"
    `include "bad_uvc_cov.sv"
    `include "bad_uvc_agent.sv"

endpackage: bad_uvc_pkg
