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

module multiplier (
    input  logic        clk,               
    input  logic        rst_n,             
    input  logic [31:0] a,                 
    input  logic [31:0] b,                 
    input  logic        in_valid_i,        
    output logic        in_ready_o,
    input  logic [1:0]  op_sel,            
    input  logic        out_ready_i,        
    output logic        out_valid_o,       
    output logic [31:0] resultado         
);

    typedef enum logic [1:0] { IDLE, MULT, RESULT } state_t;

    state_t state, next_state;

    logic [31:0] register_a, register_b;

    // Registradores internos
    logic signed   [63:0] full_result_signed;
    logic unsigned [63:0] full_result_unsigned;
    logic          valid_reg;

    logic [31:0] next_resultado;


    always_comb begin
        next_resultado = resultado;
        
        case (state)
            IDLE: begin
                out_valid_o = 1'b0;
                in_ready_o = 1'b1;
                if (in_valid_i) begin
                    next_state = MULT;
                end else begin
                    next_state = IDLE;
                end
            end
            MULT: begin
                case (op_sel)
                    // 4 Operações RISC-V
                    2'b00: begin
                        full_result_signed = ($signed(register_a) * $signed(register_b));
                        next_resultado = full_result_signed[31:0];
                    end
                    2'b01: begin 
                        full_result_signed = ($signed(register_a) * $signed(register_b));
                        next_resultado = full_result_signed[63:32];
                    end
                    2'b10: begin 
                        full_result_signed = ($signed(register_a) * $unsigned(register_b));
                        // next_resultado = full_result_signed[31:0];
                        next_resultado = full_result_signed[63:32];
                    end
                    2'b11: begin
                        full_result_unsigned = ($unsigned(register_a) * $unsigned(register_b));
                        next_resultado = full_result_unsigned[63:32];
                    end
                endcase
                in_ready_o = 1'b0;
                next_state = RESULT;
            end
            RESULT: begin
                out_valid_o = 1'b1;
                if (out_ready_i) begin
                    next_state = IDLE;
                end else begin
                    next_state = RESULT;
                end
            end
        endcase

    end


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            resultado <= next_resultado;
            case (state)
                IDLE: begin
                    register_a <= a;
                    register_b <= b;
                    state <= next_state;
                end
                MULT: begin
                    state <= next_state;
                end
                RESULT: begin
                    state <= next_state;
                end
            endcase
        end
    end
endmodule
