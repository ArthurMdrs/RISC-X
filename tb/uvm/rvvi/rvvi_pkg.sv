package rvvi_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // We use csr_addr_t from core_pkg in the tr_log
    import core_pkg::*;
    
    `include "rvvi_tdefs.sv"

    typedef virtual interface rvvi_if rvvi_vif;

    `include "rvvi_cfg.sv"
    `include "rvvi_tr.sv"
    `include "rvvi_sqr.sv"
    `include "rvvi_seq_lib.sv"
    `include "rvvi_mon.sv"
    `include "rvvi_drv.sv"
    `include "rvvi_cov.sv"
    `include "rvvi_tr_log.sv"
    `include "rvvi_agent.sv"

endpackage: rvvi_pkg
