module tb();

    // Declarar variáveis globais para o módulo
    logic [31:0] dividendo; 
    logic [31:0] divisor; 
    logic [31:0] result; 
    logic [31:0] resto;  

    // Bloco inicial para atribuição de valores e operações
    initial begin
        // Atribuir valores
        dividendo = 3;
        divisor   = 14;

        // Realizar divisão e cálculo do resto
        result = $signed (dividendo) / $signed (divisor);
        resto  = $signed(dividendo) %  $signed(divisor);  

        $display("Divisão com sinal: %d / %d = %d (resto = %d)", dividendo, divisor, result, resto);
        #1    $finish;
    end

endmodule
