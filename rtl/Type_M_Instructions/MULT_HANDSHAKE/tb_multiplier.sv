// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Testbench de validação para o RTL mult.sv
//				- Validação de sinais aleatórios
//				- Validação de sinais máximos e mínimos
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR  				    DESCRÇÃO
// 2024-08-10           0.01        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module tb_booth_multiplier;

    // Declaração dos sinais
    logic [31:0] a;
    logic [31:0] b;
    logic start;
    logic ready;         // Adiciona o sinal ready
    logic [63:0] c;
    logic valid;        // Adiciona o sinal valid
    logic done;

    logic clk;         // Sinal de clock
    logic reset_n;     // Sinal de reset ativo baixo

    logic monitor_done;

	always #5 clk = ~clk;  // Clock de 10 ns de período (100 MHz)

    // Instancia o módulo a ser testado
    booth_multiplier_32x32 dut (
        .a(a),
        .b(b),
        .start(start),
        .ready(ready),   // Conecta o sinal ready
        .c(c),
        .valid(valid),   // Conecta o sinal valid
        .done(done),
        .clk(clk),
        .reset_n(reset_n)
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

        // Inicializa os sinais
        clk = 0;
        a = 32'b0;
        b = 32'b0;
        start = 0;
        ready = 1; // Inicializa ready como 1 sempre

        reset_n = 0;
        #100;  // Mantém o reset por um tempo mais longo
        reset_n = 1;


        // Espera um pouco e depois aplica o estímulo
        #10;
        $display("Executando testes de valor fixo...");
        a = 32'h0000_0002; // Valor de exemplo para a
        b = 32'h0000_0004; // Valor de exemplo para b
        start_test();

        // Testes aleatórios
        #10;
        $display("Executando testes aleatórios...");
        repeat (10) begin
            // Gera valores aleatórios para a e b
            a = $random;
            b = $random;
            start_test();
        end

        // Teste para valores máximos
        $display("Executando teste para valores máximos...");
        #10;
        a = 32'hFFFFFFFF;
        b = 32'hFFFFFFFF;
        start_test();

        // Teste para um valor pequeno e um valor grande
        $display("Teste para valor pequeno e um grande...");
        a = 32'h00000001;
        b = 32'h7FFFFFFF;
        start_test();

        // Teste para valores negativos
      	$display("Teste para valores negativos...");
        a = 32'h80000000;
        b = 32'h80000000;
        start_test();
        
        // Teste para valores mínimos
        $display("Teste de valores mínimos...");
        a = 32'h00000000;
        b = 32'h00000000;
        start_test();

        // Finaliza a simulação
        $finish;
    end

    // Função para iniciar e aguardar o término do teste
    task start_test();
        begin
            start = 1;
            #10;
            start = 0;
            wait(valid);
            wait(done);
            #50;
        end
    endtask

    // Monitoramento dos sinais quando valid é 1
    always @(posedge clk) begin
        if (valid && !monitor_done) begin
            $display("Time: %0t | a: %d | b: %d | c: %d | valid: %b | done: %b", $time, a, b, c, valid, done);
            monitor_done = 1;
        end else if (!valid) begin
            monitor_done = 0;
        end
    end

endmodule
