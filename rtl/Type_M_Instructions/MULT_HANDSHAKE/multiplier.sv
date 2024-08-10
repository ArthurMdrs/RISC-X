// ------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Utiliza valid e ready
// ------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-08-10           0.01        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module booth_multiplier_32x32 (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic start,
    input logic ready,
    output logic [63:0] c,
    output logic valid,
    output logic done
);

    logic [31:0] A, B;
    logic [63:0] partial;
    logic [31:0] count;
    logic sign_a, sign_b;

    // Inicializa o multiplicador
    initial begin
        A = 32'b0;
        B = 32'b0;
        partial = 64'b0;
        count = 32'd0;
        sign_a = 1'b0;
        sign_b = 1'b0;
        valid = 1'b0;
        done = 1'b0;
    end

    // Função para realizar a multiplicação
    function [63:0] multiply;
        input [31:0] a;
        input [31:0] b;
        begin
            // Inicialize variáveis locais
            logic [31:0] temp_A;
            logic [31:0] temp_B;
            logic [63:0] temp_partial;
            logic [31:0] temp_count;

            // Atribua valores de entrada às variáveis locais
            temp_A = a;
            temp_B = b;
            temp_partial = 64'b0;
            temp_count = 32'd0;

            // Realize a multiplicação
            while (temp_count < 32) begin
                if (temp_B[0]) begin
                    temp_partial = temp_partial + (temp_A << temp_count);
                end
                temp_B = temp_B >> 1;
                temp_count = temp_count + 1;
            end

            // Ajuste o sinal
            if (a[31] ^ b[31]) begin
                multiply = -temp_partial;
            end else begin
                multiply = temp_partial;
            end
        end
    endfunction

    always @* begin
        if (start && ready) begin
            A = a;
            B = b;
            partial = multiply(A, B);
            valid = 1'b1;
            done = 1'b1;
        end else begin
            valid = 1'b0;
            done = 1'b0;
        end
    end

    assign c = partial;

endmodule
