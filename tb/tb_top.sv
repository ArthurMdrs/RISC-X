module tb_top;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // VIP imports - begin
        import obi_pkg::*;
    // VIP imports - end
    
    `include "tests.sv"

    bit clk, rst_n;
    bit run_clock;

    // Interfaces instances - begin
        obi_if if_obi(.clk(clk), .rst_n(rst_n));
    // Interfaces instances - end

    stub dut(
        .clk(clk),
        .rst_n(rst_n),
        // Signals from obi's interface - begin
            .req_o(if_obi.req),
            .gnt_i(if_obi.gnt),
            .addr_o(if_obi.addr),
            .we_o(if_obi.we),
            .be_o(if_obi.be),
            .wdata_o(if_obi.wdata),
            .rvalid_i(if_obi.rvalid),
            .rdata_i(if_obi.rdata)
        // Signals from obi's interface - end
    );
    
    // uvm_default_report_server rserver;

    initial begin
        clk = 0;
        rst_n = 1;
        #3 rst_n = 0;
        #3 rst_n = 1;
    end
    always #2 clk=~clk;

    initial begin
        $timeformat(-9, 3, "ns", 12); // e.g.: "       900ns"
        $dumpfile("dump.vcd");
        $dumpvars;
        
        
        // rserver = uvm_report_server::get_server();

        // Virtual interfaces send to VIPs - begin
            obi_vif_config::set(null, "uvm_test_top.agent_obi.*", "vif", if_obi);
        // Virtual interfaces send to VIPs - end

        run_test("random_test");
    end

endmodule: tb_top
