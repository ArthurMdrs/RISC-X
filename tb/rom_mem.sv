module rom_mem #(
    int AWIDTH = 8,
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] rdata,
    input  logic [AWIDTH-1:0] addr
);

// Internal memory
localparam MEMSIZE = 2**AWIDTH;
logic [MEMSIZE-1:0] [7:0] mem;

// Drive read data
always_comb begin
    rdata = mem[addr+:4];
end
    
endmodule