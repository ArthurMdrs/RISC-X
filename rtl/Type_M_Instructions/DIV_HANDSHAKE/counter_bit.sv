module counter_bit(
    input   logic       ena ,
    input   logic [30:0] A  ,
    output  logic [10:0] nBits
);
    always_comb begin
        if(ena)
            casex(A[30:0])
                31'b1xx_xxxx_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 30;end
                31'b01x_xxxx_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 29;end
                31'b001_xxxx_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 28;end
                31'b000_1xxx_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 27;end
                31'b000_01xx_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 26;end
                31'b000_001x_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 25;end
                31'b000_0001_xxxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 24;end
                31'b000_0000_1xxx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 23;end
                31'b000_0000_01xx_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 22;end
                31'b000_0000_001x_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 21;end
                31'b000_0000_0001_xxxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 20;end
                31'b000_0000_0000_1xxx__xxxx_xxxx_xxxx_xxxx:begin nBits = 19;end
                31'b000_0000_0000_01xx__xxxx_xxxx_xxxx_xxxx:begin nBits = 18;end
                31'b000_0000_0000_001x__xxxx_xxxx_xxxx_xxxx:begin nBits = 17;end
                31'b000_0000_0000_0001__xxxx_xxxx_xxxx_xxxx:begin nBits = 16;end
                31'b000_0000_0000_0000__1xxx_xxxx_xxxx_xxxx:begin nBits = 15;end
                31'b000_0000_0000_0000__01xx_xxxx_xxxx_xxxx:begin nBits = 14;end
                31'b000_0000_0000_0000__001x_xxxx_xxxx_xxxx:begin nBits = 13;end
                31'b000_0000_0000_0000__0001_xxxx_xxxx_xxxx:begin nBits = 12;end
                31'b000_0000_0000_0000__0000_1xxx_xxxx_xxxx:begin nBits = 11;end
                31'b000_0000_0000_0000__0000_01xx_xxxx_xxxx:begin nBits = 10;end
                31'b000_0000_0000_0000__0000_001x_xxxx_xxxx:begin nBits = 9;end
                31'b000_0000_0000_0000__0000_0001_xxxx_xxxx:begin nBits = 8;end
                31'b000_0000_0000_0000__0000_0000_1xxx_xxxx:begin nBits = 7;end
                31'b000_0000_0000_0000__0000_0000_01xx_xxxx:begin nBits = 6;end
                31'b000_0000_0000_0000__0000_0000_001x_xxxx:begin nBits = 5;end
                31'b000_0000_0000_0000__0000_0000_0001_xxxx:begin nBits = 4;end
                31'b000_0000_0000_0000__0000_0000_0000_1xxx:begin nBits = 3;end
                31'b000_0000_0000_0000__0000_0000_0000_01xx:begin nBits = 2;end
                31'b000_0000_0000_0000__0000_0000_0000_001x:begin nBits = 1;end
                31'b000_0000_0000_0000__0000_0000_0000_0001:begin nBits = 0;end
                default:nBits = 0;
            endcase
        else nBits = 0;
    end
endmodule