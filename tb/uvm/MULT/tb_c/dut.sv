// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-08-29           0.01        André Medeiros     	    Versão inicial.
// ----------------------------------------------------------------------------------------------------

module booth_multiplier_32x32 (
    input logic clk,                // Sinal de clock
    input logic rst_n,              // Sinal de reset ativo baixo
    input logic [31:0] a,           // 1º Operando de 32 bits
    input logic [31:0] b,           // 2º Operando de 32 bits
    input logic  in_valid_i,        // Sinal de início para começar a multiplicação
    output logic in_ready_o,        // Sinal que indica que o multiplicador está pronto para iniciar
    input logic [31:0] nclocks,     // Número de ciclos de clock para a multiplicação
    output logic [63:0] resultado,  // Resultado da multiplicação, 64 bits
    output logic out_valid_o,       // Sinal que indica que o resultado é válido
    input logic out_ready_i         // Sinal que indica que o receptor está pronto para receber novos dados
);

    logic [63:0] partial;
    logic [31:0] B_temp;
    logic [5:0] count;
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
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            A <= 32'b0;
            B <= 32'b0;
            reg_partial <= 64'b0;
            reg_valid <= 1'b0;
            count <= 6'b0;
            in_ready_o <= 1'b1; // O módulo está pronto após o reset
        end else if ( in_valid_i && in_ready_o && out_ready_i) begin
            A <= a;
            B <= b;
            reg_partial <= 64'b0;
            count <= nclocks;
            reg_valid <= 1'b0;
            in_ready_o <= 1'b0; // O módulo está processando, não pronto para novos dados
        end else if (count > 0) begin
            reg_partial <= partial;
            B <= B_temp;
            count <= count - 1;
            if (count == 1) begin
                reg_valid <= 1'b1;      // Resultado é válido
                in_ready_o <= 1'b1;     // Pronto para novos dados
            end
        end
    end

    // Atribui os valores dos registros às saídas
    assign resultado = reg_partial;           
    assign out_valid_o = reg_valid;     
    
endmodule
