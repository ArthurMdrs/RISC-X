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
    
    input  logic    [31:0] hartid_i,
    input  logic    [23:0] mtvec_i,
    
    output logic [31:0] mtvec_o
);

logic [31:0] csr_wdata_actual;
logic        csr_wen;
logic        set_initial_mtvec;

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
assign mhartid   = hartid_i;

// Machine Status Registers
mstatus_t mstatus;
assign mstatus.uie  = 1'b0; // User mode interrupt enable
assign mstatus.sie  = 1'b0; // Supervisor mode interrupt enable
assign mstatus.hie  = 1'b0; // Hypervisor mode interrupt enable
assign mstatus.mie  = 1'b0; // Machine mode interrupt enable
assign mstatus.upie = 1'b0; // User mode previous interrupt enable
assign mstatus.spie = 1'b0; // Supervisor mode previous interrupt enable
assign mstatus.ube  = 1'b0; // User mode endianess control
assign mstatus.mpie = 1'b0; // Machine mode previous interrupt enable
assign mstatus.spp  = 1'b0; // Supervisor mode previous privilege mode
assign mstatus.vs   = 2'b0; // V extension status
assign mstatus.mpp  = 2'b0; // Machine mode previous privilege mode
assign mstatus.fs   = 2'b0; // F extension status
assign mstatus.xs   = 2'b0; // X extension status
assign mstatus.mprv = 1'b0; // Modify memory PRiVilege
assign mstatus.sum  = 1'b0; // Permit Supervisor User Memory access
assign mstatus.mxr  = 1'b0; // Make eXecutable Readable
assign mstatus.tvm  = 1'b0; // Trap Virtual Memory
assign mstatus.tw   = 1'b0; // Timeout Wait
assign mstatus.tsr  = 1'b0; // Trap SRET
assign mstatus.sd   = 1'b0; // ?

// Machine Trap-Vector Base-Address Register
logic [31:0] mtvec, mtvec_n;

// Define read operation
always_comb begin
    case (csr_addr_i)
        CSR_MISA: csr_rdata_o = misa;
        
        CSR_MVENDORID: csr_rdata_o = mvendorid;
        CSR_MARCHID: csr_rdata_o = marchid;
        CSR_MIMPID: csr_rdata_o = mimpid;
        CSR_MHARTID: csr_rdata_o = mhartid;
        
        CSR_MSTATUS: csr_rdata_o = {mstatus.sd, 8'b0, mstatus.tsr, mstatus.tw, mstatus.tvm,
                                    mstatus.mxr, mstatus.sum, mstatus.mprv, mstatus.xs, mstatus.fs,
                                    mstatus.mpp, mstatus.vs, mstatus.spp, mstatus.mpie, mstatus.ube,
                                    mstatus.spie, 1'b0, mstatus.mie, 1'b0, mstatus.sie, 1'b0};
        CSR_MTVEC:csr_rdata_o = mtvec;
        
        default: csr_rdata_o = '0;
    endcase
end

// Define next values of CSRs
always_comb begin
    mtvec_n = (set_initial_mtvec) ? ({mtvec_i, 8'b0}) : (mtvec);
end

always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        set_initial_mtvec <= '1;
        mtvec <= '0;
    end
    else begin
        set_initial_mtvec <= '0;
        mtvec <= mtvec_n;
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

// Output some CSRs
assign mtvec_o = mtvec;

endmodule