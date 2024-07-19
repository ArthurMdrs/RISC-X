module register_file #(
    parameter int AWIDTH = 5,
    parameter int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] rdata1_o,
    output logic [DWIDTH-1:0] rdata2_o,
    input  logic [AWIDTH-1:0] raddr1_i,
    input  logic [AWIDTH-1:0] raddr2_i,
    input  logic [DWIDTH-1:0] wdata_i,
    input  logic [AWIDTH-1:0] waddr_i,
    input  logic              wen_i,
    input  logic              clk_i,
    input  logic              rst_n_i
);

localparam MEM_SIZE = 2**AWIDTH;

// Internal memory
// logic [DWIDTH-1:0] mem [MEM_SIZE];
logic [DWIDTH-1:0] mem [1:MEM_SIZE-1];

// Define write operation
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // mem <= '{(MEM_SIZE){'0}};
        for (int i = 1; i < MEM_SIZE; i++)
            mem[i] <= '0;
    end else begin
        if (wen_i && waddr_i != 0)
            mem[waddr_i] <= wdata_i;
        // for (int i = 1; i < MEM_SIZE; i++)
        //     if (wen_i && waddr_i == i)
        //         mem[waddr_i] <= wdata_i;
    end
end

// Define read operation
always_comb begin
    // rdata1_o = mem[raddr1_i];
    // rdata2_o = mem[raddr2_i];
    rdata1_o = (!raddr1_i) ? ('0) : (mem[raddr1_i]);
    rdata2_o = (!raddr2_i) ? ('0) : (mem[raddr2_i]);
end

// Memory address zero must be hardwired to zero
// assign mem[0] = '0;
    
endmodule