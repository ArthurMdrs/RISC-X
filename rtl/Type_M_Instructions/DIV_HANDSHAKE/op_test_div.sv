
`include "./opdiv.sv"
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
		logic 	[31:0]			nclocks		;
		 opdiv inst0opdiv(
		
				.clock		(	clock		),	
				.nreset		(	nreset		),
				.in_valid_i	(	in_valid_i	),
				.in_ready_o	(	in_ready_o	),
				.a			(	a			),
				.b			(	b			),
				.c			(	c			),
				.out_valid_o(	out_valid_o	),
				.out_ready_i(	out_ready_i	)
		
		);	
    string str [] = {"START","INITIALISE_AND_COUNTER_BITS","SET_AK_MINUEND","LOOP","UPDATE_MINUEND_RIGHT","UPDATE_MINUEND_LEFT","INCREASE_K","DONE"};
    string temp;
    initial begin
        clock = 0;
        nreset = 1;
        in_valid_i = 1;
        a= 59699056; 
        b = 87783792;
        $monitor(a,b,c);
        #2000 $finish;
     end
     always #2 clock = ~clock;
  always_ff@(negedge clock)begin
        //$display("%d %d %d %d %d %d %s",inst0opdiv.a_reg,inst0opdiv.b_reg,inst0opdiv.ena,inst0opdiv.Quatient,inst0opdiv.minuend,inst0opdiv.k ,str[inst0opdiv.state]);
        //if(temp=="START")begin 
        if(inst0opdiv.out_valid_o)begin out_ready_i <=1;
                $display(inst0opdiv.c);
                $finish;
        end

        //end
  end // $display("%d %d",inst0opdiv.ena,inst0opdiv.qbits);
  always_comb temp = str[inst0opdiv.next];
endmodule
