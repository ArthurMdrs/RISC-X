// ------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Testbench de validação para o RTL mult.sv
//				- Validação de sinais aleatórios
//				- Validação de sinais máximos e mínimos
// ------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR  				    DESCRÇÃO
// 2024-08-10           0.01        André Medeiros     	    Versão inicial.
// ------------------------------------------------------------------------------------------------

module tb_booth_multiplier;

    // Declaração dos sinais
    reg [31:0] a;
    reg [31:0] b;
    reg start;
    reg ready;         // Adiciona o sinal ready
    wire [63:0] c;
    wire valid;        // Adiciona o sinal valid
    wire done;

    // Instancia o módulo a ser testado
    booth_multiplier_32x32 uut (
        .a(a),
        .b(b),
        .start(start),
        .ready(ready),   // Conecta o sinal ready
        .c(c),
        .valid(valid),   // Conecta o sinal valid
        .done(done)
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

        $display("-------------------------------------------- INICIALIZANDO -----------------------------------------------------");

        // Inicializa os sinais
        a = 32'b0;
        b = 32'b0;
        start = 0;
        ready = 1; // Inicializa ready como 1 sempre

        // Espera um pouco e depois aplica o estímulo
        #10;
        $display("Executando testes de valor fixo...");
        a = 32'h0000_0002; // Valor de exemplo para a
        b = 32'h0000_0006; // Valor de exemplo para b
        start = 1;      // Inicia a multiplicação
        #10;          
        start = 0;
        wait(valid);
        wait(done);
        #50;

        // Testes aleatórios
        #10;
        $display("Executando testes aleatórios...");
        repeat (10) begin
            // Gera valores aleatórios para a e b
            a = $random;
            b = $random;

            start = 1;
            #10;          
            start = 0;
            wait(valid);
            wait(done); 
            #10;
        end
        #50;

        // Testes de valores limite
      	$display("Teste de valores limite...");

        // Teste para valores máximos
        $display("Executando teste para valores máximos...");
        #10;
        a = 32'hFFFFFFFF;
        b = 32'hFFFFFFFF;
        start = 1;
        #10;
        start = 0;
        wait(valid);
        #50;

        // Teste para um valor pequeno e um valor grande
        $display("Teste para valor pequeno e um grande...");
        a = 32'h00000001;
        b = 32'h7FFFFFFF;
        start = 1;
        #10;
        start = 0;
        wait(valid);
        #50;

        // Teste para valores negativos
      	$display("Teste para valores negativos...");
        a = 32'h80000000;
        b = 32'h80000000;
        start = 1;
        #10;
        start = 0;
        wait(valid);
        #50;
        
        // Teste para valores mínimos
        $display("Teste de valores mínimos...");
        a = 32'h00000000;
        b = 32'h00000000;
        start = 1;
        //ready = 1;
        #10;
        start = 0;
        //ready = 0;
        wait(valid);
        #50;

        // Finaliza a simulação
        $finish;
    end

    // Monitoramento dos sinais
    initial begin
        $monitor("Time: %0t | a: %d | b: %d | c: %d | valid: %b | done: %b", $time, a, b, c, valid, done);
    end

endmodule
