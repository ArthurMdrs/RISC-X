//Out Interface
interface a_if (input logic clock, reset);

  logic            out_ready_i;
  logic            out_valid_o; //out valid
  logic [31:0]     c;
  
endinterface

//Input Interface
interface apb_if (input logic PCLK, PRESETn);

  logic [31:0]     divisor, dividendo;
  logic                    in_valid_i; 
  logic                    in_ready_o;
  //logic [31:0]              make  nclocks;

endinterface
