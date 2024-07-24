module csr import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    input  csr_addr_t      csr_addr_i,
    input  logic    [31:0] csr_wdata_i,
    input  csr_operation_t csr_op_i,
    output logic    [31:0] csr_rdata_o,
    
    input  logic    [31:0] hart_id_i
);

logic [31:0] csr_wdata_actual;
logic        csr_wen;

// Machine ISA Register
logic [31:0] misa;
logic [ 1:0] mxl;
assign mxl = 2'b01;
assign misa = {mxl, 17'b0, ISA_M, 6'h04, ISA_F, 2'b0, ISA_C, 2'b0};

// ID registers
logic [31:0] mvendorid; // Machine Vendor ID Register
logic [31:0] marchid;   // Machine Architecture ID Register
logic [31:0] mimpid;    // Machine Implementation ID Register
logic [31:0] mhartid;   // Hart ID Register
assign mvendorid = '0;
assign marchid   = '0;
assign mimpid    = '0;
assign mhartid   = hart_id_i;

// Machine Status Registers
// Status_t mstatus;

// Define read operation
always_comb begin
    case (csr_addr_i)
        CSR_MISA: csr_rdata_o = misa;
        
        CSR_MVENDORID: csr_rdata_o = mvendorid;
        CSR_MARCHID: csr_rdata_o = marchid;
        CSR_MIMPID: csr_rdata_o = mimpid;
        CSR_MHARTID: csr_rdata_o = mhartid;
        
        default: csr_rdata_o = '0;
    endcase
end

// Define write logic
always_comb begin
    // Only RO CSRs so far
end

always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        // Only RO CSRs so far
    end
    else begin
        // Only RO CSRs so far
    end
end

// Determine actual wdata
always_comb begin
    csr_wdata_actual = csr_wdata_i;
    csr_wen    = 1'b1;

    case (csr_op_i)
        CSR_WRITE: csr_wdata_actual = csr_wdata_i;
        CSR_SET:   csr_wdata_actual = csr_wdata_i | csr_rdata_o;
        CSR_CLEAR: csr_wdata_actual = (~csr_wdata_i) & csr_rdata_o;
        CSR_READ: begin
            csr_wdata_actual = csr_wdata_i;
            csr_wen    = 1'b0;
        end
    endcase
end

endmodule