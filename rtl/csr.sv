module csr import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Porsts for CSR read/modify instructions
    input  csr_addr_t      csr_addr_i,
    input  logic    [31:0] csr_wdata_i,
    input  csr_operation_t csr_op_i,
    output logic    [31:0] csr_rdata_o,
    
    input  logic    [31:0] hartid_i,
    input  logic    [23:0] mtvec_i,
    
    // Output some CSRs
    output logic [31:0] mtvec_o,
    output logic [31:0] mepc_o,
    
    // Trap handling
    input  logic        save_pc_id_i, // Save ID PC to mepc
    input  logic        save_pc_ex_i, // Save EX PC to mepc
    input  logic [31:0] pc_id_i,
    input  logic [31:0] pc_ex_i,
    input  logic [ 4:0] exception_cause_i
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
// Machine Exception Program Counter
logic [31:0] mepc, mepc_n;
// Machine Cause Register
logic [31:0] mcause;
logic        mcause_intr_n;
logic [ 4:0] mcause_code_n;
assign mcause[31]   = 1'b0; // TODO Change this when interrupts are implemented
assign mcause[30:5] = 26'b0;
// Machine Scratch Register
logic [31:0] mscratch, mscratch_n;

// Machine Interrupt Enable Register
logic [31:0] mie, mie_n;

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
        CSR_MIE: csr_rdata_o = mie;
        CSR_MTVEC: csr_rdata_o = mtvec;
        
        CSR_MEPC: csr_rdata_o = mepc;
        CSR_MCAUSE: csr_rdata_o = mcause;
        CSR_MSCRATCH: csr_rdata_o = mscratch;
        
        default: csr_rdata_o = '0;
    endcase
end

// Define next values of CSRs
always_comb begin
    mie_n = mie;
    mtvec_n = (set_initial_mtvec) ? ({mtvec_i, 8'b0}) : (mtvec);
    mepc_n = mepc;
    mcause_intr_n = mcause[31];
    mcause_code_n = mcause[4:0];
    mscratch_n = mscratch;
    
    if (csr_wen) begin
        case (csr_addr_i)
            CSR_MEPC: begin
                if (ISA_C) mepc_n = {csr_wdata_actual[31:1], 1'b0};
                else       mepc_n = {csr_wdata_actual[31:2], 2'b0};
            end
            CSR_MCAUSE: begin
                // mcause_intr_n = csr_wdata_actual[31]; // TODO Change this when interrupts are implemented
                mcause_code_n = csr_wdata_actual[4:0];
            end
            CSR_MIE: begin
                // mcause_intr_n = csr_wdata_actual[31]; // TODO Change this when interrupts are implemented
                mie_n = csr_wdata_actual;
            end
            CSR_MSCRATCH: begin
                mscratch_n = csr_wdata_actual;
            end
        endcase
    end
    
    // Save PC to mepc when traps occur
    unique case (1'b1)
        save_pc_ex_i: mepc_n = pc_ex_i;
        save_pc_id_i: mepc_n = pc_id_i;
        default: ;
    endcase
    // Save cause of exception
    if (save_pc_ex_i || save_pc_id_i) begin
        mcause_code_n = exception_cause_i;
    end
end

// Update CSR values with next values
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        set_initial_mtvec <= '1;
        mie  <= '0;
        mtvec <= '0;
        mepc  <= '0;
        // mcause[31] <= '0;
        mcause[4:0] <= '0;
        mscratch <= '0;
    end
    else begin
        set_initial_mtvec <= '0;
        mie  <= mie_n;
        mtvec <= mtvec_n;
        mepc  <= mepc_n;
        // mcause[31] <= mcause_intr_n;
        mcause[4:0] <= mcause_code_n;
        mscratch <= mscratch_n;
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
// assign mepc_o = mepc;
// Output next value of mepc to account for writes followed by xRET 
assign mepc_o = mepc_n;

endmodule