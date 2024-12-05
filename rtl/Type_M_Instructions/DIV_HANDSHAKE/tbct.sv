`include"./counter_bit.sv"
module tb();
logic [10:0] a;
logic [31:0] in1,in2,in3;
    counter_bit ct(
        .ena(1'b1),
        .A(in1),
        .nBits(a)
    );
    initial begin 
        in1 = 100;
        #500 
        for(integer  i= 0; i<32; i++)begin       
        #1 in1 = $pow(2,i);
        #10000$display("%d %d",a,$clog2(in1),a==$clog2(in1)?"Pass":"Fail");
        end
    end
endmodule