module stub (input clk, input rst_n, 
    // Signals from obi's interface - begin
        output reg          req_o,
        input               gnt_i,
        output reg [31:0]   addr_o,
        output reg          we_o,
        output reg [ 3:0]   be_o,
        output reg [31:0]   wdata_o,
        input               rvalid_i,
        input      [31:0]   rdata_i
    // Signals from obi's interface - end
    );

    typedef enum {IDLE, WAIT_GNT, WAIT_RVALID} state_t;
    state_t state, state_n;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            state <= IDLE;
        end
        else begin
            state <= state_n;
        end
    end

    always_comb begin
        case (state)
            IDLE: begin
                // req_o = 1;
                
                case ({req_o, gnt_i})
                2'b00: begin
                    state_n = IDLE;
                end
                2'b01: begin
                    state_n = IDLE;
                end
                2'b10: begin
                    state_n = WAIT_GNT;
                end
                2'b11: begin
                    state_n = WAIT_RVALID;
                end
                default: begin
                    state_n = IDLE;
                end
                endcase
            end
            WAIT_GNT: begin
                // req_o = 1;
                
                if (gnt_i) begin
                    state_n = WAIT_RVALID;
                end
            end
            WAIT_RVALID: begin
                // req_o = 0;
                
                if (rvalid_i) begin
                    state_n = IDLE;
                end
            end
            default: begin
                // req_o = 0;
                
                state_n = IDLE;
            end
        endcase
    end
    
    always_ff @(posedge clk or negedge rst_n) begin
        if(~rst_n) begin
            req_o <= '0;
            // addr_o <= '0;
            addr_o <= 32'h8000_0000;
            we_o <= '0;
            be_o <= '0;
            wdata_o <= '0;
        end
        else begin
            case (state_n)
                IDLE: begin
                    req_o <= 1;
                    // addr_o <= $urandom();
                    // we_o <= $urandom();
                    // be_o <= $urandom();
                    wdata_o <= $urandom();
                    addr_o <= addr_o + 32'h2;
                    we_o   <= 1'b0;
                    be_o <= 4'b0011;
                end
                WAIT_GNT: begin
                    req_o <= 1;
                end
                WAIT_RVALID: begin
                    req_o <= 0;
                end
                default: begin
                    req_o <= 0;
                    addr_o <= '0;
                    we_o <= '0;
                    be_o <= '0;
                    wdata_o <= '0;
                end
            endcase
            
        end
    end
    
    always @(posedge clk) begin
        if (state == WAIT_RVALID && rvalid_i) begin
            $display("***************************");
            $display("[DUT INFO %t]", $time);
            $display("addr_o = 0x%h", addr_o);
            $display("we_o = %b", we_o);
            $display("be_o = 0x%h", be_o);
            $display("wdata_o = 0x%h", wdata_o);
            $display("rdata_i = 0x%h", rdata_i);
            $display("***************************");
        end
    end

endmodule: stub
