module ula_m (
    // Input signals
    input operation_i,                          // Seleciona entre Multiplicador ou divisor
    input [1:0] op_sel_i,                       // Operação Interna do div ou do mul
    input logic clk_i, 
    input logic rst_ni,
    input logic [31:0] alu_m_operand_1_ex_i,    
    input logic [31:0] alu_m_operand_2_ex_i,    

    // Output signals
    output logic [31:0] basic_alu_m_result1_o,  
    output logic [31:0] basic_alu_m_result2_o,  

    //Input Handshake
    input logic in_valid_i,
    output logic in_ready_o, 

    // Output handshake
    input logic out_ready_i,
    output logic out_valid_o
);

// Aux handshake
logic in_valid_i_div, in_ready_o_div, out_valid_o_div, out_ready_i_div;
logic in_valid_i_mul, in_ready_o_mul, out_valid_o_mul, out_ready_i_mul;


// Aux operands
logic [31:0] ula_m_result_a_div_aux;
logic [31:0] ula_m_result_b_div_aux;
logic [31:0] ula_m_result_a_mult_aux;

opdiv divisor(
    .clock(clk_i),
    .nreset(rst_ni),
    .a(alu_m_operand_1_ex_i),
    .b(alu_m_operand_2_ex_i),
    .c(ula_m_result_a_div_aux),
    .r(ula_m_result_b_div_aux),
    .in_valid_i(in_valid_i_div),
    .in_ready_o(in_ready_o_div), 
    .out_valid_o(out_valid_o_div),  
    .signal_division(1'b0),
    .out_ready_i(out_ready_i_div) 
);

multiplier multiplier(
    .clk(clk_i),               
    .rst_n(rst_ni),             
    .a(alu_m_operand_1_ex_i),                 
    .b(alu_m_operand_2_ex_i),                
    .in_valid_i(in_valid_i_mul),        
    .in_ready_o(in_ready_o_mul),
    .op_sel(op_sel_i),            
    .out_ready_i(out_ready_i_mul),        
    .out_valid_o(out_valid_o_mul),       
    .resultado(ula_m_result_a_mult_aux)         
);

always_comb begin
    case (operation_i) 
        0: begin // Tipo de instrução para mult
            // Handshake signals input
            in_valid_i_div = 0;
            out_ready_i_div = 0;

            in_valid_i_mul = in_valid_i;
            out_ready_i_mul = out_ready_i;

            // Handshake signals output
            in_ready_o = in_ready_o_mul;
            out_valid_o = out_valid_o_mul;

            // Output signals
            basic_alu_m_result1_o = ula_m_result_a_mult_aux;
            basic_alu_m_result2_o = 0;
        end


        1: begin // Tipo de instrução para div
            //Input handshak signals
            in_valid_i_div = in_valid_i;
            out_ready_i_div = out_ready_i;

            in_valid_i_mul = 0;
            out_ready_i_mul = 0;

            // Handshake signals output
            in_ready_o = in_ready_o_div;
            out_valid_o = out_valid_o_div;

            // Output signals
            basic_alu_m_result1_o = ula_m_result_a_div_aux;
            basic_alu_m_result2_o = ula_m_result_b_div_aux;

        end

        default: begin // Instrução diferente
            //Input handshake signals
            in_valid_i_div = 0;
            out_ready_i_div = 0;

            in_valid_i_mul = 0;
            out_ready_i_mul = 0;

            // Handshake signals output
            in_ready_o = 0;
            out_valid_o = 0;

            // Output signals
            basic_alu_m_result1_o = 0;
            basic_alu_m_result2_o = 0;

        end
    endcase

end

endmodule
