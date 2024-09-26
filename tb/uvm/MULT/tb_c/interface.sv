//Output Interface
interface out_mult_if (input logic clock, reset);

  logic                    out_ready_i;
  logic                    out_valid_o; 
  logic [63:0]             c;
  
endinterface

//Input Interface
interface in_mult_if (input logic PCLK, PRESETn);

  logic [31:0]             a, b;
  logic                    in_valid_i; 
  logic                    in_ready_o;
  logic [1:0]              op_sel       // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU

endinterface
