module mem #(
    int ADDR_WIDTH = 8,
    int DATA_WIDTH = 8,
    localparam int BEN_WIDTH = DATA_WIDTH/8
) (
    input  logic                  clk,
    input  logic                  rst_n,
    
    // Port a
    // input  logic                  en_a,
    output logic [DATA_WIDTH-1:0] rdata_a,
    input  logic [DATA_WIDTH-1:0] wdata_a,
    input  logic [ADDR_WIDTH-1:0] addr_a,
    input  logic                  wen_a,
    input  logic [BEN_WIDTH-1:0]  ben_a,
    
    // Port b
    // input  logic                  en_b,
    output logic [DATA_WIDTH-1:0] rdata_b,
    input  logic [DATA_WIDTH-1:0] wdata_b,
    input  logic [ADDR_WIDTH-1:0] addr_b,
    input  logic                  wen_b,
    input  logic [BEN_WIDTH-1:0]  ben_b
);

// Internal memory
localparam MEMSIZE = 2**ADDR_WIDTH;
// logic [MEMSIZE-1:0] [7:0] mem;
logic [7:0] mem [MEMSIZE];

// Define write operation
always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        // mem <= '{MEMSIZE{'0}};
        // mem <= '{default:'0};
        foreach (mem[i])
            mem[i] <= '0;
    end else begin
        if (wen_a) begin
            if (ben_a[0]) mem[addr_a  ] <= wdata_a[ 0+:8];
            if (ben_a[1]) mem[addr_a+1] <= wdata_a[ 8+:8];
            if (ben_a[2]) mem[addr_a+2] <= wdata_a[16+:8];
            if (ben_a[3]) mem[addr_a+3] <= wdata_a[24+:8];
        end
        else if (wen_b) begin
            if (ben_b[0]) mem[addr_b  ] <= wdata_b[ 0+:8];
            if (ben_b[1]) mem[addr_b+1] <= wdata_b[ 8+:8];
            if (ben_b[2]) mem[addr_b+2] <= wdata_b[16+:8];
            if (ben_b[3]) mem[addr_b+3] <= wdata_b[24+:8];
        end
    end
end

// Define read operation
assign rdata_a[ 0+:8] = mem[addr_a  ];
assign rdata_a[ 8+:8] = mem[addr_a+1];
assign rdata_a[16+:8] = mem[addr_a+2];
assign rdata_a[24+:8] = mem[addr_a+3];

assign rdata_b[ 0+:8] = mem[addr_b  ];
assign rdata_b[ 8+:8] = mem[addr_b+1];
assign rdata_b[16+:8] = mem[addr_b+2];
assign rdata_b[24+:8] = mem[addr_b+3];
    
endmodule