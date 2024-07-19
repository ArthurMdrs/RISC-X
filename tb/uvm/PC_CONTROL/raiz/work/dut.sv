module dut (a_if.inp in,
            a_if.outp out);

  always_ff @(posedge in.clock)
     if (in.reset) begin
        out.valid <= 0;
        out.a <= 0;
     end
     else if(in.valid) begin
        out.valid <= 1;
        out.a <= in.a + 100;
     end
     else out.valid <= 0;

endmodule

