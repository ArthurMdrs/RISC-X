// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-08-16           0.01        André Medeiros     	    Versão inicial.
// ----------------------------------------------------------------------------------------------------


module booth_multiplier_32x32 (
    input logic clk,                // Sinal de clock
    input logic reset_n,            // Sinal de reset ativo baixo
    input logic [31:0] a,           // 1º Operando de 32 bits
    input logic [31:0] b,           // 2º Operando de 32 bits
    input logic valid_in,           // Sinal de início para começar a multiplicação
    input logic ready,              // Sinal que indica que o multiplicador está pronto para iniciar
    input logic [31:0] nclocks,     // Número de ciclos de clock para a multiplicação
    output logic [63:0] c,          // Resultado da multiplicação, 64 bits
    output logic valid_out          // Sinal que indica que o resultado é válido
);

    logic [63:0] partial;           // Valor parcial da multiplicação, combinacional
    logic [31:0] B_temp;            // Variável temporária para armazenar o valor de B
    logic [5:0] count;              // Contador para controlar o número de ciclos (máximo 32)
    reg [63:0] reg_partial;         // Registro para armazenar o valor parcial da multiplicação
    reg [31:0] A, B;                // Registros para armazenar os operandos a e b
    reg reg_valid;                  // Registro para armazenar o sinal valid

    // Lógica combinacional para calcular o valor parcial
    always_comb begin
        if (count > 0) begin
            // Calcula o valor parcial com base na lógica de Booth
            partial = reg_partial;
            if (B[0]) begin
                partial = partial + (A << (32 - count)); // Soma A deslocado ao parcial se B[0] for 1
            end
            // Não desloca B aqui, apenas usa a variável temporária
            B_temp = B >> 1;
        end
    end

    // Reset síncrono e controle do módulo
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Quando reset_n é baixo, inicializa os registros com 0
            A <= 32'b0;
            B <= 32'b0;
            reg_partial <= 64'b0;
            reg_valid <= 1'b0;
            count <= 6'b0;
        end else if (valid_in && ready) begin
            // Quando valid_in e ready estão ativos, inicializa os registros com os operandos e configura o contador para nclocks
            A <= a;
            B <= b;
            reg_partial <= 64'b0;       // Inicializa reg_partial com 0
            count <= nclocks;           // Usa nclocks para definir o número de ciclos
            reg_valid <= 1'b0;
        end else if (count > 0) begin
            // Atualiza reg_partial com o valor calculado pela lógica combinacional
            reg_partial <= partial;
            B <= B_temp;                // Atualiza B com a variável temporária
            count <= count - 1;         // Decrementa o contador
            if (count == 1) begin
                reg_valid <= 1'b1;      // Marca o resultado como válido
            end
        end
    end

    // Atribui os valores dos registros às saídas
    assign c = reg_partial;           // Resultado da multiplicação
    assign valid_out = reg_valid;     // Sinal que indica se o resultado é válido
    
endmodule
