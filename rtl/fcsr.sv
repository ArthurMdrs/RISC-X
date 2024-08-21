module fcsr (
    input logic [31:0] write_data,  // Dados de escrita
    input logic write_enable,       // Enable de escrita
    input logic read_enable,        // Enable de leitura
    output logic [31:0] read_data   // Dados de saida
);

    typedef struct packed {
        logic [4:0] fflags;    // Bits 0-4: Flags de exceção
        logic [2:0] frm;       // Bits 5-7: Modo de arredondamento
        logic [23:0] reserved; // Bits 8-31: Reservado
    } fcsr_t;

    fcsr_t fcsr_reg;

    // Escrita no FCSR
    always_ff @(posedge write_enable) begin
        if (write_enable) begin
            fcsr_reg <= write_data;
        end
    end

    // Leitura do FCSR
    always_comb begin
        if (read_enable) begin
            read_data = fcsr_reg;
        end
    end

endmodule
