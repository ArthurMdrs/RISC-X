package obi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "riscx_mem_model.sv"
    
    import obi_tdefs_pkg::*;

    typedef virtual interface obi_if obi_vif;

    `include "obi_cntxt.sv"
    `include "obi_cfg.sv"
    `include "obi_tr.sv"
    `include "obi_seqr.sv"
    `include "obi_seq_lib.sv"
    `include "obi_mon.sv"
    `include "obi_drv.sv"
    `include "obi_cov.sv"
    `include "obi_agent.sv"

endpackage: obi_pkg
