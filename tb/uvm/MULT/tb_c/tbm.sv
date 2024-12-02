module tb();

    // Declarar variáveis globais para o módulo
    logic [31:0] a; 
    logic [31:0] b; 
    logic [63:0] result, result2; 
    logic [31:0] resto;  

    // Bloco inicial para atribuição de valores e operações
    initial begin
        // Atribuir valores
        a   = 32'h8cc03ce6;
        b   = 32'h8abcabd0;
        //Operação
        result = $signed (a) * $signed (b);
        result2 = $unsigned (a) * $unsigned (b);
        //print
        //$display("----- MUltiplicação com sinal -----");
        $display("(DEC)Muliplicação com sinal: %d %d = %d ", a, b, result);
        $display("(HEX)Muliplicação com sinal: %h %h = %h ", a, b, result);
        //$display("(BIN)Muliplicação com sinal: %b %b = %b ", a, b, result);
        $display("----- MUltiplicação sem sinal -----");
        $display("(DEC)Muliplicação com sinal: %d %d = %d ", a, b, result2);
        $display("(HEX)Muliplicação com sinal: %h %h = %h ", a, b, result2);
        $display("(BIN)Muliplicação com sinal: %b %b = %b ", a, b, result2);
        #1    $finish;
    end

endmodule
