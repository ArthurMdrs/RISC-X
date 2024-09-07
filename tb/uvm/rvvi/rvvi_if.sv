interface rvvi_if #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
)
(
    input logic clk, 
    input logic rst_n
);

    import uvm_pkg::*;    
    `include "uvm_macros.svh"
    import rvvi_pkg::*;
    
    logic                      valid      ;   // Valid event
    logic [63:0]               order      ;   // Unique event order count (no gaps or reuse)

    logic [(ILEN-1):0]         insn       ;   // Instruction bit pattern
    logic                      trap       ;   // State update without instruction retirement
    logic                      debug_mode ;   // Retired instruction executed in debug mode

    // Program counter
    logic [(XLEN-1):0]         pc_rdata   ;   // PC of instruction

    // X Registers
    logic [31:0][(XLEN-1):0]   x_wdata    ;   // X data value
    logic [31:0]               x_wb       ;   // X data writeback (change) flag

    // F Registers
    logic [31:0][(FLEN-1):0]   f_wdata    ;   // F data value
    logic [31:0]               f_wb       ;   // F data writeback (change) flag

    // V Registers
    // logic [31:0][(VLEN-1):0]   v_wdata    ;   // V data value
    // logic [31:0]               v_wb       ;   // V data writeback (change) flag

    // Control and Status Registers
    logic [4095:0][(XLEN-1):0] csr        ;   // Full CSR Address range
    logic [4095:0]             csr_wb     ;   // CSR writeback (change) flag

    // Atomic Memory Control
    // logic                      lrsc_cancel;   // Implementation defined cancel

    // Optional
    logic [(XLEN-1):0]         pc_wdata   ;   // PC of next instruction
    logic                      intr       ;   // (RVFI Legacy) Flag first instruction of trap handler
    logic                      halt       ;   // Halted  instruction
    logic [1:0]                ixl        ;   // XLEN mode 32/64 bit
    logic [1:0]                mode       ;   // Privilege mode of operation

    // task reset_sigs();
    
    // endtask
    
    task collect_tr(rvvi_tr tr);
        while (!valid) begin
            @(posedge clk);
        end
        
        tr.order        = order         ;
        tr.insn         = insn          ;
        tr.trap         = trap          ;
        tr.debug_mode   = debug_mode    ;
        tr.pc_rdata     = pc_rdata      ;
        tr.x_wdata      = x_wdata       ;
        tr.x_wb         = x_wb          ;
        tr.f_wdata      = f_wdata       ;
        tr.f_wb         = f_wb          ;
        tr.csr          = csr_wb        ;
        tr.pc_wdata     = pc_wdata      ;
        tr.intr         = intr          ;
        tr.halt         = halt          ;
        tr.ixl          = ixl           ;
        tr.mode         = mode          ;
        
        // TODO: is this okay??
        // This fixes monitor getting duplicate transactions
        #1step;
        // @(posedge clk);
    endtask : collect_tr
    
    task wait_clk();
        @(posedge clk);
    endtask : wait_clk
    
    



    // Signals for transaction recording
    bit monstart, drvstart;
    
    // Signal to control monitor activity
    bit got_tr;
    // Test transaction
    rvvi_tr tr = new("TR");

    task rvvi_reset();
        @(negedge rst_n);
        monstart = 0;
        drvstart = 0;
        disable send_to_dut;
    endtask

    // Gets a transaction and drive it into the DUT
    task send_to_dut(rvvi_tr req);
        // Logic to start recording transaction
        @(negedge clk);

        // trigger for transaction recording
        drvstart = 1'b1;

        // Drive logic 
        tr.copy(req);
        `uvm_info("RVVI INTERFACE", $sformatf("Driving transaction to DUT:%s", tr.convert2string()), UVM_HIGH)
        got_tr = 1'b1;
        @(negedge clk);

        // Reset trigger
        drvstart = 1'b0;
    endtask : send_to_dut

endinterface : rvvi_if
