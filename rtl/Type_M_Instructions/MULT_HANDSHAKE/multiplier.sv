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
    input logic [31:0] a,
    input logic [31:0] b,
    input logic start,
    input logic ready,
    output logic [63:0] c,
    output logic valid,
    output logic done,
    input logic clk,
    input logic reset_n
);

    logic [63:0] partial;
    logic [5:0] count;

    // Registros para armazenar os valores
    reg [31:0] A, B;
    reg [63:0] reg_partial;
    reg reg_valid, reg_done;

    // Reset síncrono
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            A <= 32'b0;
            B <= 32'b0;
            reg_partial <= 64'b0;
            reg_valid <= 1'b0;
            reg_done <= 1'b0;
            count <= 6'b0;
        end else if (start && ready) begin
            A <= a;
            B <= b;
            reg_partial <= 64'b0;
            count <= 6'd32;
            reg_done <= 1'b0;
            reg_valid <= 1'b0;
        end else if (count > 0) begin
            if (B[0])
                reg_partial <= reg_partial + (A << (32-count));
            B <= B >> 1;
            count <= count - 1;
            if (count == 1) begin
                reg_done <= 1'b1;
                reg_valid <= 1'b1;
            end
        end
    end

    assign c = reg_partial;
    assign valid = reg_valid;
    assign done = reg_done;

endmodule
