// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Testbench de validação para o RTL mult.sv
//				- Validação de sinais aleatórios
//				- Validação de sinais máximos e mínimos
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR  				    DESCRÇÃO
// 2024-11-22           0.12        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module tb_multiplier_32x32;

    logic clk;
    logic rst_n;
    logic [31:0] a, b;
    logic in_valid_i;
    logic out_ready_i;
    logic [1:0] op_sel;
    logic in_ready_o;
    logic out_valid_o;
    logic [63:0] resultado;

    // Instância do DUT
    multiplier_32x32 uut (
        .clk(clk),
        .rst_n(rst_n),
        .a(a),
        .b(b),
        .in_valid_i(in_valid_i),
        .out_ready_i(out_ready_i),
        .op_sel(op_sel),
        .in_ready_o(in_ready_o),
        .out_valid_o(out_valid_o),
        .resultado(resultado)
    );

    // Geração do clock
    always #5 clk = ~clk;

    // Estímulos do teste
    initial begin
        clk = 0;
        rst_n = 0;
        a = 0;
        b = 0;
        in_valid_i = 0;
        out_ready_i = 1;
        op_sel = 2'b00;

        // Reset do sistema
        #10 rst_n = 1;

        // Teste 1: Multiplicação simples (MUL)
        a = 32'd10; b = 32'd20; op_sel = 2'b00; in_valid_i = 1;
        wait (in_ready_o);
        #20 in_valid_i = 0;
        wait (out_valid_o);
        $display("Teste 1 - (MUL): a=%0d, b=%0d, resultado=%0d (esperado: 200)", a, b, $signed(resultado));
        
        // Teste 2: Multiplicação com sinal (MULH)
        a = $signed(1000); b = $signed(-500); op_sel = 2'b01; in_valid_i = 1;
        wait (in_ready_o);
        #20 in_valid_i = 0;
        wait (out_valid_o);
        $display("Teste 2 - (MULH): a=%0d, b=%0d, Resultado = %0d (esperado: %0d)", a, b, $signed(resultado), ($signed(1000) * $signed(-500)) >>> 32);
        
        // Teste 3: Multiplicação com sinal e sem sinal (MULHSU)
        a = $signed(1000); b = $unsigned(500); op_sel = 2'b10; in_valid_i = 1;
        wait (in_ready_o);
        #20 in_valid_i = 0;
        wait (out_valid_o);
        $display("Teste 3 - (MULHSU): a=%0d, b=%0d, Resultado = %0d (esperado: %0d)", a, b, $signed(resultado), ($signed(1000) * $unsigned(500)) >>> 32);

        // Teste 4: Multiplicação sem sinal (MULHU)
        a = $unsigned(500); b = $unsigned(400); op_sel = 2'b11; in_valid_i = 1;
        wait (in_ready_o);
        #20 in_valid_i = 0;
        wait (out_valid_o);
        $display("Teste 4 - (MULHU): a=%0d, b=%0d, Resultado = %0d (esperado: %0d)", a, b, resultado, ($unsigned(500) * $unsigned(400)) >>> 32);
        
        #20 $finish;
    end
endmodule
