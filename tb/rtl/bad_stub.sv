module stub #(
    bit ENABLE_PRINT = 0
    )(
    input clk, 
    input rst_n, 

    // Interface with data memory
    input  logic [31:0] dmem_rdata_i,
    output logic [31:0] dmem_wdata_o,
    output logic [31:0] dmem_addr_o,
    output logic        dmem_wen_o,
    output logic  [3:0] dmem_ben_o,

    // Interface with instruction memory
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o
    );
    
    reg [31:0]   addr_o;
    reg          we_o;
    reg [ 3:0]   be_o;
    reg [31:0]   wdata_o;
        
    assign dmem_wdata_o = wdata_o;
    assign dmem_addr_o  = addr_o ;
    assign dmem_wen_o   = we_o   ;
    assign dmem_ben_o   = be_o   ;
    
    assign imem_addr_o  = addr_o ;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            // addr_o <= '0;
            addr_o <= 32'h8000_0000;
            we_o <= 1'b0;
            be_o <= 4'b0011;
            wdata_o <= '0;
        end
        else begin
            wdata_o <= $urandom();
            addr_o <= addr_o + 32'h2;
            we_o   <= 1'b0;
            be_o <= 4'b0011;
        end
    end
    
    always @(posedge clk) begin
        if (ENABLE_PRINT) begin
            $display("***************************");
            $display("[DUT INFO %t]", $time);
            $display("addr_o = 0x%h", addr_o);
            // $display("we_o = %b", we_o);
            $display("be_o = 0x%h", be_o);
            $display("wdata_o = 0x%h", wdata_o);
            $display("dmem_rdata_i = 0x%h", dmem_rdata_i);
            $display("imem_rdata_i = 0x%h", imem_rdata_i);
            $display("***************************");
        end
    end

endmodule: stub
