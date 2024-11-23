// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `top` para verificação UVM do multiplicador binário de 32x32 bits
//             - Classe principal que instancia o ambiente de verificação completo.
//             - Conecta os componentes principais: `env`, `coverage_in`, `coverage_out`, driver, sequencer, monitor, scoreboard.
//             - Inicializa o DUT e gerencia os testes UVM, incluindo a geração de relatórios e logs.
//             - Executa os cenários de teste, coordenando o fluxo de simulação.
// ----------------------------------------------------------------------------------------------------
// / RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------
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

   // APB clock and reset are the same
   logic PCLK, PRESETn;
   assign PCLK = clock;
   assign PRESETn = ~reset;

   // Input and output interface instance for DUT
   in_mult_if in_vi(.*);
   out_mult_if out_vi(.*);

  //Instance DUT
   booth_multiplier_32x32 testediv( 
    .clk(clock)                   ,
    .rst_n(~reset)                ,
    .a(in_vi.b)              ,
    .b(in_vi.a)                ,
    .in_valid_i(in_vi.in_valid_i)    ,
    .in_ready_o(in_vi.in_ready_o)    ,         
    .resultado(out_vi.c)             ,
    .out_valid_o(out_vi.out_valid_o) ,
    .out_ready_i(out_vi.out_ready_i) ,
    .op_sel (in_vi.op_sel)       
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
      uvm_config_db #(virtual in_mult_if)::set(null, "uvm_test_top.env_h.agent_in_h.*", "in_vi", in_vi);
      uvm_config_db #(virtual out_mult_if)::set(null, "uvm_test_top.env_h.agent_out_h.*", "out_vi", out_vi);

      run_test("test");
   end
endmodule

