// The collection of signal ports for DUT and testbench
interface a_if (input logic clock, reset);

  logic valid; // handshake signal: a is valid at rising clock when valid=1
  logic [31:0] a, b, c; // not using parameter to keep it simpler
  logic ready;

  logic  [31:0] nclocks;    //Retorna o número de ciclo de clocks da operação 
  logic                 done    ; //indicação de conclusão da operaçãoi
  // The interface input port is for incoming data.
  modport inp (input clock, reset, input valid, input a, input b, output c, output nclocks, output ready, output done);

  // The interface output port is for outcoming data.
  modport outp (input clock, reset, output valid, output a, output b, input c, input nclocks, input ready, input done);

endinterface

