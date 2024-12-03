// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Módulo multiplicador binário de 32x32bits
//				- Baseado no algoritmo de multiplicação binária de booth
//				- Handshake (valid e ready)
//				- Lógica Combinacional para calcular o valor parcial
//				- Lógica Sequencial para reset síncrono e controle do módulo
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR     				DESCRIÇÃO
// 2024-12-03           0.14        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module multiplier_32x32 (
    input  logic        clk,               
    input  logic        rst_n,             
    input  logic [31:0] a,                 
    input  logic [31:0] b,                 
    input  logic        in_valid_i,        
    input  logic        out_ready_i,       
    input  logic [1:0]  op_sel,            
    output logic        in_ready_o,        
    output logic        out_valid_o,       
    output logic [31:0] resultado          
);
    // Registradores internos
    logic signed   [63:0] full_result_signed;
    logic unsigned [63:0] full_result_unsigned;
    logic          valid_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            in_ready_o              <= 1'b1;
            out_valid_o             <= 1'b0;
            resultado               <= 32'b0;
            full_result_signed      <= 64'b0;
            full_result_unsigned    <= 64'b0;
            valid_reg               <= 1'b0;
        end else begin
            // Handshake para entrada
            if (in_ready_o && in_valid_i) begin
                in_ready_o <= 1'b0;
                case (op_sel)
                    // 4 Operações RISC-V
                    2'b00: full_result_signed <= ($signed(a) * $signed(b));
                    2'b01: full_result_signed <= ($signed(a) * $signed(b));
                    2'b10: full_result_signed <= ($signed(a) * $unsigned(b));
                    2'b11: full_result_unsigned <= ($unsigned(a) * $unsigned(b));
                endcase
                valid_reg <= 1'b1;
            end
            // Handshake para saída
            if (valid_reg && out_ready_i) begin
                case (op_sel)
                    2'b00: begin
                        resultado   <= full_result_signed;
                    end            
                    2'b01: begin
                        resultado   <= full_result_signed >>> 32;
                    end     
                    2'b10: begin
                        resultado   <= full_result_signed >>> 32;
                    end   
                    2'b11: begin
                        resultado   <= full_result_unsigned >>> 32;
                    end
                endcase
                out_valid_o <= 1'b1;
                valid_reg   <= 1'b0;
                in_ready_o  <= 1'b1;
            end else begin
                out_valid_o <= 1'b0;
            end
        end
    end
endmodule
