interface out_div_if (input logic clock, reset);

  logic                   out_ready_i;
  logic                   out_valid_o; 
  logic signed [31:0]     c, r;

endinterface

interface in_div_if (input logic PCLK, PRESETn);

  logic signed [31:0]     divisor, dividendo;
  logic                   in_valid_i;         //Handshake
  logic                   in_ready_o;         //Handshake
  logic                   signal_division;

endinterface
