// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-09-23           0.11        André Medeiros     	    Versão inicial.
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
    input logic out_ready_i,        // Sinal que indica que o receptor está pronto para receber novos dados
    input logic [1:0] op_sel       // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU
);

    // Declaramos operandos assinados e não assinados
    // Isso é necessário para suportar operações com e sem sinal
    logic signed [31:0] signed_a;       // Versão com sinal do operando a
    logic signed [31:0] signed_b;       // Versão com sinal do operando b
    logic [31:0] unsigned_a;            // Versão sem sinal do operando a
    logic [31:0] unsigned_b;            // Versão sem sinal do operando b
    logic signed [63:0] signed_result;  // Resultado da multiplicação com sinal
    logic [63:0] unsigned_result;       // Resultado da multiplicação sem sinal

    // Variáveis intermediárias para a lógica do algoritmo de Booth
    logic [63:0] partial;               // Resultado parcial durante a multiplicação
    logic [31:0] B_temp;                // Valor temporário de B usado no deslocamento
    logic [5:0] count;                  // Contador de ciclos da operação de multiplicação
    reg [63:0] reg_partial;             // Registrador do valor parcial do produto
    reg [31:0] A, B;                    // Registradores para os operandos A e B
    reg reg_valid;                      // Sinal para indicar quando o resultado é válido

    // Atribuições para os sinais de entrada com e sem sinal
    assign signed_a = a;
    assign signed_b = b;
    assign unsigned_a = a;
    assign unsigned_b = b;

    // Lógica combinacional para calcular o valor parcial
    always_comb begin
        if (count > 0) begin
            // Se o contador for maior que 0, continuamos a multiplicação
            partial = reg_partial;     // Carrega o valor parcial do resultado atual
            if (B[0]) begin
                // Se o bit menos significativo de B for 1, adicionamos A deslocado
                partial = partial + (A << (32 - count)); // Desloca A e adiciona ao parcial
            end
            // B é deslocado para a direita
            B_temp = B >> 1;
        end else begin
            // Se o contador for 0, não atualizamos o parcial nem B
            partial = reg_partial;    // Mantém o valor parcial atual
            B_temp = B;               // Mantém o valor de B atual
        end
    end

    // Lógica sequencial que controla o fluxo da multiplicação
    always_ff @(posedge clk or negedge rst_n) begin
        if (rst_n == 0) begin
            // Quando rst_n é 0, resetamos os sinais
            A <= 32'b0;               // Resetamos o operando A
            B <= 32'b0;               // Resetamos o operando B
            reg_partial <= 64'b0;     // Resetamos o resultado parcial
            reg_valid <= 1'b0;        // Indicamos que o resultado não é válido
            count <= 6'b0;            // Resetamos o contador
            in_ready_o <= 1'b1;       // O multiplicador está pronto para receber novos dados
        end 
        else if (in_valid_i && in_ready_o && out_ready_i) begin
            // Quando os sinais de controle estão prontos e válidos:
            // O multiplicador inicia a operação
            A <= a;                   // Carrega o valor de a no registrador A
            B <= b;                   // Carrega o valor de b no registrador B
            reg_partial <= 64'b0;     // Inicializa o resultado parcial com zero
            count <= 6'd32;           // Inicializa o contador para 32 ciclos (tamanho dos operandos)
            reg_valid <= 1'b0;        // O resultado ainda não é válido
            in_ready_o <= 1'b0;       // Indica que o multiplicador está ocupado
        end 
        else if (count > 0) begin
            // Durante o processo de multiplicação (enquanto o contador > 0):
            reg_partial <= partial;   // Atualiza o resultado parcial com o valor calculado
            B <= B_temp;              // Atualiza B com o valor temporário deslocado
            count <= count - 1;       // Decrementa o contador de ciclos
            if (count == 1) begin
                // Quando o contador chega a 1, indicamos que o resultado está pronto
                reg_valid <= 1'b1;    // O resultado se torna válido
                in_ready_o <= 1'b1;   // O multiplicador está pronto para novos dados
            end
        end
    end

    // Lógica para selecionar o resultado correto dependendo do tipo de multiplicação
    always_comb begin
        case (op_sel)
            2'b00: begin // Operação MUL: Multiplicação normal com sinal
                resultado = signed_a * signed_b;  // Multiplica dois números com sinal
            end
            2'b01: begin // Operação MULH: Bits superiores do produto com sinal
                signed_result = signed_a * signed_b;  // Multiplica dois números com sinal
                resultado = signed_result[63:32];     // Pega os 32 bits superiores do resultado
            end
            2'b10: begin // Operação MULHSU: Bits superiores com a assinado e b sem sinal
                signed_result = signed_a * unsigned_b; // Multiplica A com sinal e B sem sinal
                resultado = signed_result[63:32];      // Pega os 32 bits superiores do resultado
            end
            2'b11: begin // Operação MULHU: Bits superiores de ambos os operandos sem sinal
                unsigned_result = unsigned_a * unsigned_b; // Multiplica dois números sem sinal
                resultado = unsigned_result[63:32];        // Pega os 32 bits superiores do resultado
            end
            default: begin
                resultado = 64'b0; // Se o tipo de operação for inválido, o resultado é 0
            end
        endcase
    end

    // Atribuição do sinal de validade à saída
    assign out_valid_o = reg_valid;     

endmodule
