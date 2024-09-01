interface a_if (input logic clock, reset);

  logic            out_ready_i;
  logic            out_valid_o; //out valid
  logic [31:0]     c;
  logic            nclocks;

endinterface

interface apb_if (input logic PCLK, PRESETn);

  logic [31:0]     divisor, dividendo;
  logic            in_valid_i; 
  logic            in_ready_o;

endinterface


/*
  div testediv( 
    .clock(clock)                ,
    .nreset(~reset)              ,
    .in_valid_i(in.in_valid_i)   ,
    .in_ready_o(in.in_ready)     ,
    .a(in.dividendo)             ,
    .b(in.divisor)               ,
    .c(out.c)                    ,
    .nclocks(in.nclocks)         , 
    .out_valid_o(in.valid)       ,
    .out_ready_i(in.out_ready)   
  );
*/