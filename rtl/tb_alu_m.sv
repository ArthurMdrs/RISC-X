module alu_m_tb();
    

    logic clk_i, rst_ni;
    
    logic in_valid_i, in_ready_o, out_valid_o;
    logic out_ready_i = 1'b1;

    logic operation_i;
    logic [1:0] op_sel_i;

    logic [31:0] alu_m_operand_1_ex_i, alu_m_operand_2_ex_i;

    logic [31:0] basic_alu_m_result1_o, basic_alu_m_result2_o;

    // Instancia da ULA

    ula_m ula(.*);

    initial begin
        clk_i = 0;
        rst_ni = 0;
    end

    always begin
       #2
       clk_i = ~clk_i; 
    end

    initial begin
        #2
        rst_ni = 1;
    end

    initial begin
        
        ////////////////////////////////////////////////
        ///////////// INICIO DA TRANSAÇÂO //////////////
        ////////////////////////////////////////////////
        @(posedge clk_i)
        operation_i = 0;
        op_sel_i = 0;
        alu_m_operand_1_ex_i = 2;
        alu_m_operand_2_ex_i = 3;
        in_valid_i = 0;
        
        @(posedge clk_i)

        in_valid_i = 1;

        @(posedge clk_i)
        in_valid_i = 0;
        
        @(posedge out_valid_o)
        repeat(10)@(posedge clk_i)
        operation_i = 1;
        op_sel_i = 0;
        alu_m_operand_1_ex_i = 2;
        alu_m_operand_2_ex_i = 3;
        in_valid_i = 0;

        repeat(10)@(posedge clk_i)
        @(posedge out_valid_o)
        in_valid_i = 0;
        @(posedge clk_i)
        in_valid_i = 1;
        $finish;
       
    end



endmodule