package clknrst_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // import clknrst_tdefs_pkg::*;
    `include "clknrst_tdefs.sv"

    typedef virtual interface clknrst_if clknrst_vif;

    `include "clknrst_cfg.sv"
    `include "clknrst_tr.sv"
    `include "clknrst_sqr.sv"
    `include "clknrst_seq_lib.sv"
    `include "clknrst_mon.sv"
    `include "clknrst_drv.sv"
    `include "clknrst_cov.sv"
    `include "clknrst_agent.sv"

endpackage: clknrst_pkg
