// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-09-16           0.11        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module booth_multiplier_32x32 (
    input logic clk,                // Sinal de clock
    input logic rst_n,              // Sinal de reset ativo baixo
    input logic [31:0] a,           // 1º Operando de 32 bits
    input logic [31:0] b,           // 2º Operando de 32 bits
    input logic in_valid_i,         // Sinal de início para começar a multiplicação
    output logic in_ready_o,        // Sinal que indica que o multiplicador está pronto para iniciar
    output logic [63:0] resultado,  // Resultado da multiplicação, 64 bits
    output logic out_valid_o,       // Sinal que indica que o resultado é válido
    input logic out_ready_i         // Sinal que indica que o receptor está pronto para receber novos dados
);

    logic [63:0] partial;
    logic [31:0] B_temp;
    logic [5:0] count;               // Contador de ciclos
    reg [63:0] reg_partial;
    reg [31:0] A, B;
    reg reg_valid;

    // Lógica combinacional para calcular o valor parcial
    always_comb begin
        if (count > 0) begin
            partial = reg_partial;
            if (B[0]) begin
                partial = partial + (A << (32 - count)); // Lógica do algoritmo de Booth
            end
            B_temp = B >> 1;
        end else begin
            partial = reg_partial;  // Mantém o valor atual se count = 0
            B_temp = B;            // Mantém o valor de B se count = 0
        end
    end

    // Lógica sequencial
    always_ff @(posedge clk or negedge rst_n) begin
        if (rst_n == 0) begin // Se rst_n = 0 (reset ativo)
            // Quando o reset está ativo (rst_n = 0), o sistema é reinicializado.
            // Os seguintes registradores são definidos para seus valores iniciais:
            A <= 32'b0;               // Reseta o operando A para 0
            B <= 32'b0;               // Reseta o operando B para 0
            reg_partial <= 64'b0;     // Reseta o resultado parcial para 0
            reg_valid <= 1'b0;        // Reseta o sinal de validade para 0 (não válido)
            count <= 6'b0;            // Reseta o contador para 0
            in_ready_o <= 1'b1;       // Define o sinal de prontidão para 1 (pronto para aceitar novos dados)
        end 
        else if (in_valid_i && in_ready_o && out_ready_i) begin // Se rst_n = 1 (reset inativo)
            // Quando o reset não está ativo (rst_n = 1) e todas as condições de início são atendidas:
            // A lógica normal de operação é executada:
            A <= a;                  // Carrega o valor de entrada a para o registrador A
            B <= b;                  // Carrega o valor de entrada b para o registrador B
            reg_partial <= 64'b0;    // Inicializa o resultado parcial para 0
            count <= 6'd32;          // Define o contador para 32 ciclos
            reg_valid <= 1'b0;       // Define o sinal de validade para 0 (não válido)
            in_ready_o <= 1'b0;      // Define o sinal de prontidão para 0 (não pronto para novos dados)
        end 
        else if (count > 0) begin // Se rst_n = 1 (reset inativo)
            // Quando o contador é maior que 0, atualiza o resultado parcial e o registrador B.
            reg_partial <= partial;  // Atualiza o resultado parcial com o valor calculado
            B <= B_temp;             // Atualiza B com o valor temporário B_temp
            count <= count - 1;      // Decrementa o contador
            if (count == 1) begin
                reg_valid <= 1'b1;   // Quando o contador chega a 1, o resultado é válido
                in_ready_o <= 1'b1; // Define o sinal de prontidão para 1 (pronto para aceitar novos dados)
            end
        end
    end

    // Atribui os valores dos registros às saídas
    assign resultado = reg_partial;           
    assign out_valid_o = reg_valid;     

endmodule
