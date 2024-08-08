module tb_multiplier;

    // Sinais de teste
    logic clk;
    logic reset;
    logic start;
    logic [31:0] a;
    logic [31:0] b;
    logic [31:0] c;
    logic done;

    // Instancia o módulo multiplier
    multiplier uut (
        .clk(clk),
        .reset(reset),
        .start(start),
        .a(a),
        .b(b),
        .c(c),
        .done(done)
    );

    // Geração de clock
    always #5 clk = ~clk;

    // Reset generation
    initial begin
        clk = 0;
        reset = 0;
        #10;
        reset = 1;
        #10;
        reset = 0;  // Desativa o reset após 10 unidades de tempo
    end

    // Sequência de estímulos
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
        $dumpvars(0, tb_multiplier);

        $display("-------------------------------------------- INICIALIZANDO -----------------------------------------------------");

        // Inicialização
        start = 0;
        a = 32'b0;
        b = 32'b0;

        // Testes aleatórios
        $display("Executando testes aleatórios...");
        repeat (10) begin
            // Gera valores aleatórios para a e b
            a = $random;
            b = $random;
            // Gera o sinal de start
            start = 1;
            #10;          // Espera 10 unidades de tempo para garantir que o start seja registrado
            start = 0;

            // Espera pela conclusão
            wait(done);

            // Mostra os valores e o resultado
            $display("Time: %0t | a = %0d, b = %0d, Resultado = %0d", $time, a, b, c);

            // Espera um pouco antes de iniciar o próximo teste
            #10;
        end

        // Testes de valores limite
      	$display("Teste de valores limite...");
        // Teste para valores máximos
        a = 32'hFFFFFFFF;
        b = 32'hFFFFFFFF;
        start = 1;
        #10;
        start = 0;
        wait(done);
        $display("Time: %0t | a = %0d, b = %0d, Resultado = %0d", $time, a, b, c);

      
      	$display("Teste de valores mínimos...");
        // Teste para valores mínimos
        a = 32'h00000000;
        b = 32'h00000000;
        start = 1;
        #10;
        start = 0;
        wait(done);
        $display("Time: %0t | a = %0d, b = %0d, Resultado = %0d", $time, a, b, c);

      	
      	$display("Teste para valor pequeno e um grande...");
        // Teste para um valor pequeno e um valor grande
        a = 32'h00000001;
        b = 32'hFFFFFFFF;
        start = 1;
        #10;
        start = 0;
        wait(done);
        $display("Time: %0t | a = %0d, b = %0d, Resultado = %0d", $time, a, b, c);


      	$display("Teste para valores negativos...");
        // Teste para valores negativos
        a = 32'h80000000;
        b = 32'h80000000;
        start = 1;
        #10;
        start = 0;
        wait(done);
        $display("Time: %0t | a = %0d, b = %0d, Resultado = %0d", $time, a, b, c);

        // Finaliza a simulação
        $finish;
    end

endmodule
