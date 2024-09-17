module top;
   import uvm_pkg::*;
   import test_pkg::*;

   // Clock generator
   logic clock;
   initial begin
     clock = 0;
     forever #5 clock = ~clock;
   end

   // Reset generator
   logic reset;
   initial begin
     reset = 1;
     repeat(2) @(negedge clock);
     reset = 0;
   end

  //Reset generator 1 (test)
  //  initial begin
  //    reset = 1;
  //    #32 reset = 0; //i
  //    #10 reset = 1; //m 
  //    repeat(2) @(negedge clock);
  //    reset = 0;
  //  end

  //Reset generator 2

  // initial begin
  //   // Início com reset ativo
  // reset = 1;
  
  // // Espera 2 pulsos de clock antes de liberar o reset
  // repeat(2) @(negedge clock);
  // reset = 0;
  
  // // Loop infinito para alternar o reset conforme o ciclo desejado
  // forever begin
  //   // Espera 50 pulsos de clock com reset em 0
  //   repeat(50) @(negedge clock);
  //   reset = 1;  // Ativa o reset
    
  //   // Espera 2 pulsos de clock com reset em 1
  //   repeat(2) @(negedge clock);
  //   reset = 0;  // Desativa o reset
  // end
  // end
   
   // APB clock and reset are the same
   logic PCLK, PRESETn;
   assign PCLK = clock;
   assign PRESETn = ~reset;

   // Input and output interface instance for DUT
   apb_if in(.*);
   a_if out(.*);

  //Instance DUT
   booth_multiplier_32x32 testediv( 
    .clk(clock)                   ,
    .rst_n(~reset)                ,
    .a(in.dividendo)              ,
    .b(in.divisor)                ,
    .in_valid_i(in.in_valid_i)    ,
    .in_ready_o(in.in_ready_o)    ,         
    .resultado(out.c)             ,
    .out_valid_o(out.out_valid_o) ,
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
      uvm_config_db #(virtual apb_if)::set(null, "uvm_test_top.env_h.agent_in_h.*", "apb_vi", in);
      uvm_config_db #(virtual a_if)::set(null, "uvm_test_top.env_h.agent_out_h.*", "a_vi", out);

      run_test("test");
   end
endmodule

