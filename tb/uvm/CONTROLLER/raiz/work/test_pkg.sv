`include "uvm_macros.svh"
`include "bvm_macros.svh" // macros created by Brazil-IP / UFCG

package test_pkg;

  import uvm_pkg::*;
  import bvm_pkg::*;

  `include "trans.svh"
  `include "sequence.svh"
  typedef uvm_sequencer #(a_tr) sequencer;
  `include "driver.svh"
  `include "monitor.svh"
  `include "agent.svh"
  `include "coverage_in.svh"
  `include "coverage_out.svh"
  `include "refmod.svh"
  `include "env.svh"
  `include "test.svh"

endpackage
  
