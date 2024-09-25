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

   // APB clock and reset are the same
   logic PCLK, PRESETn;
   assign PCLK = clock;
   assign PRESETn = ~reset;

   // input and output interface instance for DUT
   in_div_if in(.*);
   out_div_if out(.*);

   opdiv testediv( 
    .clock(clock)                       ,
    .nreset(~reset)                     ,
    .a(in.dividendo)                    ,
    .b(in.divisor)                      ,
    .c(out.c)                           ,
    .in_valid_i(in.in_valid_i)          ,
    .in_ready_o(in.in_ready_o)          ,
    .out_valid_o(out.out_valid_o)       ,
    .out_ready_i(out.out_ready_i)   
  );

   initial begin
      // vendor dependent waveform recording
      `ifdef INCA
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
      uvm_config_db #(virtual in_div_if)::set(null, "uvm_test_top.env_h.agent_in_h.*", "in_vi", in);
      uvm_config_db #(virtual out_div_if)::set(null, "uvm_test_top.env_h.agent_out_h.*", "out_vi", out);

      run_test("test");
   end
endmodule

