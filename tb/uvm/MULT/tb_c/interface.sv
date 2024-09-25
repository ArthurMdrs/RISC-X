//Output Interface
interface out_mult_if (input logic clock, reset);

  logic            out_ready_i;
  logic            out_valid_o; //out valid
  logic [63:0]     c;
  
endinterface

//Input Interface
interface in_mult_if (input logic PCLK, PRESETn);

  logic [31:0]     a, b;
  logic                    in_valid_i; 
  logic                    in_ready_o;

endinterface
