    interface obi_if #(int XLEN=32, int ALEN=32) (input clk, input rst_n);

        import uvm_pkg::*;    
        `include "uvm_macros.svh"
        import obi_pkg::*;
    
        // Address phase signals
        logic              req;
        logic              gnt;
        logic [ALEN  -1:0] addr;
        logic              we;
        logic [XLEN/8-1:0] be;
        logic [XLEN  -1:0] wdata;
        
        // Response phase signals
        logic              rvalid;
        logic              rready;
        logic [XLEN  -1:0] rdata;

        // Signals for transaction recording
        bit monstart, drvstart;
        
        // Signal to control monitor activity
        bit got_tr;
        // Test transaction
        obi_tr tr = new("TR");

        task obi_reset();
            @(negedge rst_n);
            monstart = 0;
            drvstart = 0;
            disable send_to_dut;
        endtask

        // Gets a transaction and drive it into the DUT
        task send_to_dut(obi_tr req);
            // Logic to start recording transaction
            @(negedge clk);

            // trigger for transaction recording
            drvstart = 1'b1;

            // Drive logic 
            tr.copy(req);
            `uvm_info("OBI INTERFACE", $sformatf("Driving transaction to DUT:%s", tr.convert2string()), UVM_HIGH)
            got_tr = 1'b1;
            @(negedge clk);

            // Reset trigger
            drvstart = 1'b0;
        endtask : send_to_dut

        // Collect transactions
        task collect_tr(obi_tr req);
            // Logic to start recording transaction
            @(posedge clk iff got_tr);
            got_tr = 1'b0;
            
            // trigger for transaction recording
            monstart = 1'b1;

            // Collect logic 
            req.copy(tr);
            `uvm_info("OBI INTERFACE", $sformatf("Collected transaction:%s", req.convert2string()), UVM_HIGH)
            @(posedge clk);

            // Reset trigger
            monstart = 1'b0;
        endtask : collect_tr

    endinterface : obi_if
    