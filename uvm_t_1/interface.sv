// The collection of signal ports for DUT and testbench
interface a_if (input logic clock, reset);

  logic valid; // handshake signal: a is valid at rising clock when valid=1
  logic [31:0] a, b, c; // not using parameter to keep it simpler
  logic ready;

  // The interface input port is for incoming data.
  modport inp (input clock, reset, input valid, input a, b, c);

  // The interface output port is for outcoming data.
  modport outp (input clock, reset, output valid, output a, b, c);

endinterface

