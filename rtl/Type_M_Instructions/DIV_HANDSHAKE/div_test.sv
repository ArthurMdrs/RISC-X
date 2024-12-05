`include "./opdiv.sv"
module tb();
		parameter [31:0] numero_de_testes = 200;
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
		opdiv divisor(
		
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
	logic [31:0] fail_test;
	string str [] = {"IDLE","INITIALISE_AND_COUNTER_BITS","SET_AK_MINUEND","LOOP","UPDATE_MINUEND_RIGHT","UPDATE_MINUEND_LEFT","INCREASE_K","DONE"};
    string temp2;
	//always #1000 $finish;
	  always_comb temp2 = str[divisor.state];
		initial begin 
			clock 		= 	0	;
		//	in_valid_i 	= 	0	;

		#1 	nreset 		= 	1	;
		#1  nreset 		= 	0	;
		#1	nreset 		= 	1	;
	
		//	in_valid_i = 	1	;
		end
		always#3 clock = ~clock;
		always #(2*32*200) $finish;
		logic [31:0] counter1,counter2,temp;
		always_ff@(posedge clock,negedge nreset) 
			if(!nreset) begin
				out_ready_i <= 		0	;	
				counter1 	<= 		0	;
				counter2 	<= 		0	;
				temp  		<= 1;//$urandom_range(100,1);
				a 			<=	$urandom_range($pow(2,31),1);
				b 			<=	$urandom_range($pow(2,31),1);
				fail_test   <= 0;
				in_valid_i <=0;
			end
			else if(out_valid_o) 
			begin
				if(counter2 <= numero_de_testes)begin
					if(counter1 <= temp)begin counter1 <= counter1 + 1;
						out_ready_i <= 0;
					end else begin
						fail_test <= c != a/b ? fail_test +1:fail_test;
						$display("%d %d  %d %d %s \n",a,b,c,a/b,c== a/b ? "Pass":"Fail");
						out_ready_i <=	1 					;
						a 			<=	$urandom_range($pow(2,12),-$pow(2,12));
						b 			<=	$urandom_range($pow(2,6),-$pow(2,6));	
						counter1 	<= 	0					;
						counter2 	<= counter2 + 1			;
						temp  		<= $urandom_range(100,1)	;
						//if(c!= a/b)$finish;
					end
				end
				else begin
					$display("	pass,	fail,	total");
					$display(numero_de_testes-fail_test,fail_test,numero_de_testes);
					//$finish;
				end

			end
			else in_valid_i <= a > 0 && b > 0;


/*
  	assert property (@(posedge clock) disable iff (!nreset) in_valid_i |-> ##[1:$] in_ready_o);
  	assert property (@(posedge clock) disable iff (!nreset) (in_valid_i && !in_ready_o |=> $stable(a)));
  	assert property (@(posedge clock) disable iff (!nreset) (in_valid_i && !in_ready_o |=> $stable(b)));

	assert property (@(posedge clock) disable iff (!nreset) out_valid_o |-> ##[1:$] out_ready_i);
  	assert property (@(posedge clock) disable iff (!nreset) (out_valid_o && !out_ready_i |=> $stable(c)));

	wire cnt_up =  in_valid_i &&  in_ready_o;
	wire cnt_dn = out_valid_o && out_ready_i;
	int outstanding_tr;
	always_ff @(posedge clock, negedge nreset) begin
		if (!nreset) begin
			outstanding_tr <= '0;
		end
		else begin
			case ({cnt_up, cnt_dn})
				2'b00: outstanding_tr <= outstanding_tr;
				2'b01: outstanding_tr <= outstanding_tr - 1;
				2'b10: outstanding_tr <= outstanding_tr + 1;
				2'b11: outstanding_tr <= outstanding_tr;
				default: outstanding_tr <= '0;
			endcase
		end
	end

  	assert property (@(posedge clock) disable iff (!nreset) (out_valid_o |-> (outstanding_tr > 0)));
  	assert property (@(posedge clock) disable iff (!nreset) (outstanding_tr inside {0, 1}));


	int unsigned cnt_clks;
	always_ff @(posedge clock, negedge nreset) begin
		if (!nreset) begin
			cnt_clks <= '0;
		end
		else begin
			cnt_clks <= cnt_clks + 1;
			if (cnt_clks >= 10_000)
				$finish;
		end
	end
	
*/
endmodule
