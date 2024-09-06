package riscx_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import clknrst_pkg::*;
    import bad_uvc_pkg::*;

    `include "riscx_vseqr.sv"
    `include "riscx_vseq_lib.sv"
    `include "riscx_env.sv"
    
    `include "tests.sv"

endpackage: riscx_pkg