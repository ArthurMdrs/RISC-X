package riscx_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import obi_pkg::*;

    typedef uvm_config_db#(virtual interface obi_if) obi_vif_config;
    typedef virtual interface obi_if obi_vif;

    `include "riscx_env.sv"
    
    `include "tests.sv"

endpackage: riscx_pkg