// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Testbench de validação para o RTL mult.sv
//				- Validação de sinais aleatórios
//				- Validação de sinais máximos e mínimos
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR  				    DESCRÇÃO
// 2024-09-23           0.11        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module tb_booth_multiplier;

    // Declaração dos sinais
    logic clk;                // Sinal de clock
    logic rst_n;              // Sinal de reset ativo baixo
    logic [31:0] a;           // 1º Operando de 32 bits
    logic [31:0] b;           // 2º Operando de 32 bits
    logic in_valid_i;         // Sinal valid de entrada
    logic in_ready_o;         // Sinal ready (saída)
    logic out_ready_i;        // Sinal ready de saída (entrada)
    logic [63:0] resultado;   // Resultado da multiplicação, 64 bits
    logic out_valid_o;        // Sinal valid de saída
    logic [1:0] op_sel;      // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU

    // Clock de 10 ns de período (100 MHz)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Gerar reset
    initial begin
        // Aplicar reset
        rst_n = 0;
        in_valid_i = 0;
        out_ready_i = 1; // Inicialmente assume-se que o receptor está pronto
        @(posedge clk);
        rst_n = 1;
        @(posedge clk); // Aguarda um ciclo após desativar o reset
    end

    // Instancia o módulo a ser testado
    booth_multiplier_32x32 dut (
        .clk(clk),
        .rst_n(rst_n),
        .a(a),
        .b(b),
        .in_valid_i(in_valid_i),
        .in_ready_o(in_ready_o),
        .out_ready_i(out_ready_i),
        .resultado(resultado),
        .out_valid_o(out_valid_o),
        .op_sel(op_sel)
    );

    // Procedimento inicial do testbench
    initial begin
        `ifdef XCELIUM
            $shm_open("waves.shm");
            $shm_probe("AS");
        `endif
        `ifdef VCS
            $vcdpluson;
        `endif
        `ifdef QUESTA
            $wlfdumpvars();
        `endif
        $dumpfile("waves.vcd");
        $dumpvars(0, tb_booth_multiplier);

        $display("Simulação iniciada...");

        // Testes de valor fixo com diferentes tipos de operação
        $display("Executando testes de valor fixo...");
        a = 32'h0000_0002; 
        b = 32'h0000_0004; 

        // Teste com MUL (op_sel = 00)
        op_sel = 2'b00; // MUL: Multiplicação com sinal
        start_test();

        // Teste com MULH (op_sel = 01)
        op_sel = 2'b01; // MULH: Parte alta da multiplicação com sinal
        start_test();

        // Teste com MULHSU (op_sel = 10)
        op_sel = 2'b10; // MULHSU: Parte alta com a com sinal e b sem sinal
        start_test();

        // Teste com MULHU (op_sel = 11)
        op_sel = 2'b11; // MULHU: Parte alta sem sinal
        start_test();

        // Testes aleatórios
        $display("Executando testes aleatórios...");
        repeat (10) begin
            a = $random;
            b = $random;
            op_sel = $random % 4; // Gera valores aleatórios para o tipo de operação
            start_test();
        end

        // Teste para valores máximos
        $display("Executando teste para valores máximos...");
        a = 32'hFFFFFFFF;
        b = 32'hFFFFFFFF;
        op_sel = 2'b00; // Multiplicação normal
        start_test();

        // Teste para um valor pequeno e um valor grande
        $display("Teste para valor pequeno e um grande...");
        a = 32'h00000001;
        b = 32'h7FFFFFFF;
        op_sel = 2'b00; // Multiplicação normal
        start_test();

        // Teste para valores negativos
        $display("Teste para valores negativos...");
        a = 32'h80000000;
        b = 32'h80000000;
        op_sel = 2'b00; // Multiplicação normal
        start_test();

        // Teste para valores mínimos
        $display("Teste de valores mínimos...");
        a = 32'h00000000;
        b = 32'h00000000;
        op_sel = 2'b00; // Multiplicação normal
        start_test();

        $finish;
    end

    // Função para iniciar e aguardar o término do teste
    task start_test();
        begin
            // Inicia o teste
            in_valid_i = 0;
            @(posedge clk);       // Aguarda um ciclo de clock antes de começar
            in_valid_i = 1;       // Envia os dados válidos
            @(posedge clk);       // Aguarda um ciclo de clock
            in_valid_i = 0;       // Dados não são mais válidos após o ciclo de clock

            // Aguarda até o resultado estar pronto (out_valid_o = 1)
            wait(out_valid_o);   
            @(posedge clk);
            
            $display("Time: %0t | a: %d | b: %d | resultado: %d | op_sel: %b | in_valid_i: %b | out_valid_o: %b | in_ready_o: %b | out_ready_i: %b", 
                $time, a, b, resultado, op_sel, in_valid_i, out_valid_o, in_ready_o, out_ready_i);
        end
    endtask

endmodule
