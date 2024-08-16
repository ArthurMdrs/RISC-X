// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Testbench de validação para o RTL mult.sv
//				- Validação de sinais aleatórios
//				- Validação de sinais máximos e mínimos
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR  				    DESCRÇÃO
// 2024-08-16           0.01        André Medeiros     	    		    Versão inicial.
// ----------------------------------------------------------------------------------------------------

module tb_booth_multiplier;

    // Declaração dos sinais
    logic clk;                // Sinal de clock
    logic reset_n;            // Sinal de reset ativo baixo
    logic [31:0] a;           // 1º Operando de 32 bits
    logic [31:0] b;           // 2º Operando de 32 bits
    logic valid_in;           // Sinal valid de entrada
    logic ready;              // Sinal ready
    logic [31:0] nclocks;     // Sinal para contar número de clocks
    logic [63:0] c;           // Resultado da multiplicação, 64 bits
    logic valid_out;          // Sinal valid de saída

    always #5 clk = ~clk;  // Clock de 10 ns de período (100 MHz)

    // Instancia o módulo a ser testado
    booth_multiplier_32x32 dut (
        .clk(clk),
        .reset_n(reset_n),
        .a(a),
        .b(b),
        .valid_in(valid_in),
        .ready(ready),
        .nclocks(nclocks),
        .c(c),
        .valid_out(valid_out)
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
        valid_in = 0;
        ready = 1;              // Inicializa ready sempre como 1 (Multiplicador pronto para iniciar)
        nclocks = 32'd32;       // Valor para o número esperado de ciclos (Número do maior operando = 32 cíclos)

        $display("Executando testes de valor fixo...");
        a = 32'h0000_0002; // Valor de exemplo para a = 2
        b = 32'h0000_0004; // Valor de exemplo para b = 4
        start_test();

        a = 32'h0000_0002; // Valor de exemplo para a = 2
        b = 32'h0000_0006; // Valor de exemplo para b = 6
        start_test();

        a = 32'h0000_0002; // Valor de exemplo para a = 2
        b = 32'h0000_000A; // Valor de exemplo para b = 10
        start_test();

        a = 32'h0000_0002; // Valor de exemplo para a = 2
        b = 32'h0000_0014; // Valor de exemplo para b = 20
        start_test();

        // Testes aleatórios
        $display("Executando testes aleatórios...");
        repeat (10) begin
            // Gera valores aleatórios para a e b
            a = $random;
            b = $random;
            start_test();
        end

        // Teste para valores máximos
        $display("Executando teste para valores máximos...");
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
        
        a = 32'h00000000;
        b = 32'h00000001;
        start_test();

        // Finaliza a simulação
        $finish;
    end

    // Função para iniciar e aguardar o término do teste
    task start_test();
        begin
            reset_n = 0;
            #100;              // Mantém o reset por um tempo mais longo
            reset_n = 1;
            valid_in = 1;
            #10;                // Espera um ciclo de clock
            valid_in = 0;
            wait(valid_out);
            #50;                // Espera que o resultado esteja disponível
            $display("Time: %0t | a: %d | b: %d | c: %d | valid_in: %b | valid_out: %b | ready: %b | nclocks: %d", 
                $time, a, b, c, valid_in, valid_out, ready, nclocks);
        end
    endtask

endmodule
