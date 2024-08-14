/*
    Arquivo para implementação da interface OBI

    Criado por: Túlio Tavares
    Data: 14/07/2024


    Ultima modificação: 14/07/2024
    Descrição: Adição de sinais iniciais para lidar com buscas na memória de instrução (IF Stage);
    Autor: Túlio Tavares
*/

interface OBI_if #(
    parameter logic WIDTH = 32) (input logic clk, input logic reset_n);
    
    // SIGNALS Declaration
    logic req;
    logic gnt;
    logic [WIDTH-1:0] addr;
    logic we;
    logic [4:0] be;
    logic [WIDTH-1:0] wdata;
    logic rvalid;
    logic [WIDTH-1:0] rdata;

    modport MANAGER(
        output req,
        output addr,
        output we,
        output be,
        output wdata,
        input gnt,
        input rvalid,
        input rdata
    );

    modport SUBORDINATE(
        input req,
        input addr,
        input we,
        input be,
        input wdata,
        output gnt,
        output rvalid,
        output rdata
    );

endinterface