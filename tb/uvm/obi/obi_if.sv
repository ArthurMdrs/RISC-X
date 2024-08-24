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
    obi_tr tr1 = new("TR");

    task obi_reset();
        // @(negedge rst_n);
        // monstart = 0;
        // drvstart = 0;
        // disable send_to_dut;
        gnt = 1'b0;
        rvalid = 1'b0;
        rdata = '0;
    endtask

    // Gets a transaction and drive it into the DUT
    task send_to_dut(obi_tr req);
        // Logic to start recording transaction
        @(negedge clk);

        // trigger for transaction recording
        drvstart = 1'b1;

        // Drive logic 
        tr1.copy(req);
        `uvm_info("OBI INTERFACE", $sformatf("Driving transaction to DUT:%s", tr1.convert2string()), UVM_HIGH)
        got_tr = 1'b1;
        @(negedge clk);

        // Reset trigger
        drvstart = 1'b0;
    endtask : send_to_dut

    // Collect transactions
    // task collect_tr(obi_tr req);
    //     // Logic to start recording transaction
    //     @(posedge clk iff got_tr);
    //     got_tr = 1'b0;
        
    //     // trigger for transaction recording
    //     monstart = 1'b1;

    //     // Collect logic 
    //     req.copy(tr);
    //     `uvm_info("OBI INTERFACE", $sformatf("Collected transaction:%s", req.convert2string()), UVM_HIGH)
    //     @(posedge clk);

    //     // Reset trigger
    //     monstart = 1'b0;
    // endtask : collect_tr
    
    task addr_ch_collect_tr(obi_tr tr);
        while (!(req===1'b1 && gnt===1'b1)) begin
            // `uvm_info("OBI INTERFACE", $sformatf("{req, gnt} = 2'b%b", {req, gnt}), UVM_LOW)
            @(posedge clk);
        end
            // `uvm_info("OBI INTERFACE", $sformatf("{req, gnt} = 2'b%b", {req, gnt}), UVM_LOW)
        
        tr.addr = addr;
        tr.we = we;
        tr.be = be;
        tr.wdata = wdata;
        
        @(posedge clk);
    endtask : addr_ch_collect_tr
    
    task resp_ch_collect_tr(obi_tr tr);
        while (!(rvalid===1'b1 && rready===1'b1)) begin
            // `uvm_info("OBI INTERFACE", $sformatf("{rvalid, rready} = 2'b%b", {rvalid, rready}), UVM_LOW)
            @(posedge clk);
        end
        
        `uvm_info("OBI INTERFACE", $sformatf("rdata = 0x%h", rdata), UVM_LOW)
        tr.rdata = rdata;
        
        @(posedge clk);
    endtask : resp_ch_collect_tr
    
    task addr_ch_drive_tr(obi_tr tr);
        int wait_gnt_cycles;
        wait_gnt_cycles = tr.wait_gnt_cycles;
        gnt = 1'b0;
        
        // repeat(wait_gnt_cycles) begin
        //     @(posedge clk);
        // end
        // rvalid = 1'b1;
        
        while(!(req===1'b1 && gnt===1'b1)) begin
            if(wait_gnt_cycles == 0)
                gnt = 1'b1;
            if(req===1'b1 && wait_gnt_cycles != 0)
                wait_gnt_cycles--;
            @(posedge clk);
        end
        gnt = 1'b0;
        
    endtask : addr_ch_drive_tr
    
    task resp_ch_drive_tr(obi_tr tr);
        int wait_rvalid_cycles;
        wait_rvalid_cycles = tr.wait_rvalid_cycles;
        rvalid = 1'b0;
        
        repeat (tr.wait_rvalid_cycles) begin
            @(posedge clk);
        end
        
        rvalid = 1'b1;
        rdata = tr.rdata;
        
        wait (rready===1'b1);
        
        @(posedge clk);
        rvalid = 1'b0;
        
        // while(!(rvalid===1'b1 && rready===1'b1)) begin
        //     if(wait_rvalid_cycles == 0)
        //         rvalid = 1'b1;
        //     if(rvalid===1'b1 && wait_rvalid_cycles != 0)
        //         wait_rvalid_cycles--;
        //     @(posedge clk);
        // end
        
    endtask : resp_ch_drive_tr
    
    assert property (@(posedge clk) disable iff (!rst_n) req |-> ##[1:$] gnt);
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(addr)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(we)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(be)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> $stable(wdata)));
    assert property (@(posedge clk) disable iff (!rst_n) (req && !gnt |=> req));

    assert property (@(posedge clk) disable iff (!rst_n) rvalid |-> ##[1:$] rready);
    assert property (@(posedge clk) disable iff (!rst_n) (rvalid && !rready |=> $stable(rdata)));
    assert property (@(posedge clk) disable iff (!rst_n) (rvalid && !rready |=> rvalid));
        
endinterface : obi_if
