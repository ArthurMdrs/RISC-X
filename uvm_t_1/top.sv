module top;
   import uvm_pkg::*;
   import test_pkg::*;

   // Clock generator
   logic clock;
   initial begin
     clock = 0;
     forever #5 clock = ~clock;
   end

   // reset generator
   logic reset;
   initial begin
     reset = 1;
     repeat(2) @(negedge clock);
     reset = 0;
   end

   // input and output interface instance for DUT
   a_if in(.*);
   a_if out(.*);
   dut d(.*);

   initial begin
      // vendor dependent waveform recording
      `ifdef XCELIUM
        $shm_open("waves.shm");
        $shm_probe("AS");
      `endif
      `ifdef VCS
        $vcdpluson;
      `endif
      `ifdef QUESTA
        $wlfdumpvars();
      `endif

      // register the input and output interface instance in the database
      uvm_config_db #(virtual a_if)::set(null, "uvm_test_top.env_h.agent_in_h.*", "a_vi", in);
      uvm_config_db #(virtual a_if)::set(null, "uvm_test_top.env_h.agent_out_h.*", "a_vi", out);

      run_test("test");
   end
endmodule

