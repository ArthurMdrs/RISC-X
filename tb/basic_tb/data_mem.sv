module data_mem #(
    int AWIDTH = 8,
    int DWIDTH = 8,
    localparam int MWIDTH = DWIDTH/8
) (
    output logic [DWIDTH-1:0] rdata,
    input  logic [DWIDTH-1:0] wdata,
    input  logic [AWIDTH-1:0] addr,
    input  logic              wen,
    input  logic              clk,
    input  logic              rst_n,
    // input  logic [3:0]        rdata_mask,
    input  logic [MWIDTH-1:0] wdata_mask
);

// Internal memory
localparam MEMSIZE = 2**AWIDTH;
logic [MEMSIZE-1:0] [7:0] mem;

// Define write operation
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        mem <= '{MEMSIZE{'0}};
    end else begin
        if (wen)
            foreach(wdata_mask[i])
                mem[addr+i] <= (wdata_mask[i]) ? wdata[i*8+:8] : mem[addr+i];
    end
end

// Define read operation
assign rdata = mem[addr+:4];
    
endmodule