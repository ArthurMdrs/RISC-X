

module tb();
		logic 					clock		;
		logic 					nreset		;
		logic 					in_valid_i	;
		logic 					in_ready_o	;
		logic   signed   [31:0] a    		;
		logic 	signed	[31:0]  b			;
		logic 	signed	[31:0]  c			;
		logic 					out_valid_o	;
		logic					out_ready_i	;
    logic signal_division;
		logic 	[31:0]			nclocks,pass		;
		opdiv inst0opdiv(
		
				.clock		      (	clock		    ),	
				.nreset		      (	nreset		  ),
				.in_valid_i	    (	in_valid_i	),
				.in_ready_o	    (	in_ready_o	),
				.a			        (	a			      ),
				.b			        (	b			      ),
				.c			        (	c			      ),
				.out_valid_o    (	out_valid_o	),
				.out_ready_i    (	out_ready_i	),
        .signal_division(signal_division)
//        .signal_division( 0     )
		
		);	
    string str [] = {"IDLE","INITIALISE_AND_COUNTER_BITS","SET_AK_MINUEND","LOOP,UPDATE_MINUEND_RIGHT","UPDATE_MINUEND_LEFT","INCREASE_K,DONE"};
    string temp;
    initial begin
        clock = 0;
        nreset = 1;
        #1
        nreset = 0;
        #1
        nreset = 1;
        in_valid_i = 1;      
        out_ready_i =1;
        //out_ready_i = 0;
       // $monitor("%d %d %d",a,b,c);
        #10000000000 $finish;
     end
     always #2 clock = ~clock;
  always_ff@(posedge clock, negedge nreset)begin
        //$display("%d %d %d %d %d %d %s",inst0opdiv.a_reg,inst0opdiv.b_reg,inst0opdiv.ena,inst0opdiv.Quatient,inst0opdiv.minuend,inst0opdiv.k ,str[inst0opdiv.state]);
        //if(temp=="START")begin 
        if(!nreset)begin
            a    <= 2147483648;
            b    <= 9565;
            pass <= 0 ;
            signal_division <= 1;
        end else if(inst0opdiv.out_valid_o)begin 
                
              if($abs(a)/$abs(b) == inst0opdiv.c && $abs(a%b) == inst0opdiv.r || inst0opdiv.r == 32'hffff_ffff || inst0opdiv.c == 32'hffff_ffff ||inst0opdiv.r == 0 |inst0opdiv.c ==0)begin
                pass  <= pass +1;
            a    <= -2147483648;
            b    <= -9565;
                signal_division <= 1;
                $display("%d/%d =  %d,%d,%d",inst0opdiv.a,inst0opdiv.b,inst0opdiv.c,inst0opdiv.r,a%b,"pass");
              end
              else  begin
                $display("%d/%d =  %d,%d, %d %d",inst0opdiv.a,inst0opdiv.b,inst0opdiv.c,inst0opdiv.r,a/b,a%b,"-");
                //$display("%d/%d =  %d,%d, %d ",inst0opdiv.a,inst0opdiv.b,inst0opdiv.c,inst0opdiv.r,$abs(a)%$abs(b),uint'(a)/unit'(b));

                pass <= 0;
                a    <= a;
                b    <= b;
                $finish;
              end
        end

        //end
  end // $display("%d %d",inst0opdiv.ena,inst0opdiv.qbits);
  always_comb temp = str[inst0opdiv.next];
endmodule
