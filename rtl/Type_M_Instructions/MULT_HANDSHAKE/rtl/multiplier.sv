// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-11-22           0.12        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module multiplier_32x32 (
    input  logic        clk,               // Sinal de clock
    input  logic        rst_n,             // Sinal de reset ativo baixo
    input  logic [31:0] a,                 // 1º Operando de 32 bits
    input  logic [31:0] b,                 // 2º Operando de 32 bits
    input  logic        in_valid_i,        // Sinal de início para começar a multiplicação
    output logic        in_ready_o,        // Sinal que indica que o multiplicador está pronto para iniciar
    output logic [63:0] resultado,         // Resultado da multiplicação, 64 bits
    output logic        out_valid_o,       // Sinal que indica que o resultado é válido
    input  logic        out_ready_i,       // Sinal que indica que o receptor está pronto para receber novos dados
    input  logic [1:0]  op_sel             // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU
);
    // Registradores internos
    logic signed   [63:0] full_result;
    logic          valid_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            in_ready_o  <= 1'b1;
            out_valid_o <= 1'b0;
            resultado   <= 64'b0;
            full_result <= 64'b0;
            valid_reg   <= 1'b0;
        end else begin
            // Handshake para entrada
            if (in_ready_o && in_valid_i) begin
                in_ready_o <= 1'b0;
                case (op_sel)
                    2'b00: full_result <= ($signed(a) * $signed(b));     // MUL: Produto normal com sinal
                    2'b01: full_result <= ($signed(a) * $signed(b)) >>> 32;     // MULH: Bits superiores Produto completo com sinal
                    2'b10: full_result <= ($signed(a) * $unsigned(b)) >>> 32;   // MULHSU: Bits superiores Produto com sinal e sem sinal
                    2'b11: full_result <= ($unsigned(a) * $unsigned(b)) >>> 32; // MULHU: Bits superiores Produto sem sinal
                endcase
                valid_reg <= 1'b1;
            end
            // Handshake para saída
            if (valid_reg && out_ready_i) begin
                resultado <= full_result;
                out_valid_o <= 1'b1;
                valid_reg   <= 1'b0;
                in_ready_o  <= 1'b1;
            end else begin
                out_valid_o <= 1'b0;
            end
        end
    end
endmodule
