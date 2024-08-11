// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Utiliza valid e ready
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-08-10           0.01        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module booth_multiplier_32x32 (
    input logic [31:0] a,           // 1º Operando de 32 bits
    input logic [31:0] b,           // 2º Operando de 32 bits
    input logic start,              // Sinal de início para começar a multiplicação
    input logic ready,              // Sinal que indica que o multiplicador está pronto para iniciar
    output logic [63:0] c,          // Resultado da multiplicação, 64 bits
    output logic valid,             // Sinal que indica que o resultado é válido
    output logic done,              // Sinal que indica que a multiplicação foi concluída
    input logic clk,                // Sinal de clock
    input logic reset_n             // Sinal de reset ativo baixo
);

    logic [63:0] partial;           // Valor parcial da multiplicação
    logic [5:0] count;              // Contador para controlar o número de ciclos (máximo 32)

    // Registros para armazenar os valores
    reg [31:0] A, B;                // Registros para armazenar os operandos a e b
    reg [63:0] reg_partial;         // Registro para armazenar o valor parcial da multiplicação
    reg reg_valid, reg_done;        // Registros para armazenar os sinais valid e done
   
    // Reset síncrono
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Quando reset_n é baixo, inicializa os registros com 0
            A <= 32'b0;
            B <= 32'b0;
            reg_partial <= 64'b0;
            reg_valid <= 1'b0;
            reg_done <= 1'b0;
            count <= 6'b0;
        end else if (start && ready) begin
            // Quando start e ready estão ativos, inicializa os registros com os operandos e configura o contador para 32
            A <= a;
            B <= b;
            reg_partial <= 64'b0;
            count <= 6'd32;
            reg_done <= 1'b0;
            reg_valid <= 1'b0;
        end else if (count > 0) begin
            // Se o contador for maior que 0, realiza a multiplicação
            if (B[0])
                reg_partial <= reg_partial + (A << (32-count)); // Soma A deslocado ao parcial se B[0] for 1
            B <= B >> 1;                                       // Desloca B para a direita
            count <= count - 1;                                // Decrementa o contador
            if (count == 1) begin
                reg_done <= 1'b1;                              // Marca a operação como concluída
                reg_valid <= 1'b1;                             // Marca o resultado como válido
            end
        end
    end

    // Atribui os valores dos registros às saídas
    assign c = reg_partial;       // Resultado da multiplicação
    assign valid = reg_valid;     // Sinal que indica se o resultado é válido
    assign done = reg_done;       // Sinal que indica se a multiplicação foi concluída

endmodule
