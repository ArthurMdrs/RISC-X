`include "./div.sv"

module testbench();


       logic [31:0] num1;
       logic [31:0] num2;
       logic [31:0] out1;
			 logic  [31:0] nclocks;
			 logic nreset	;
       logic clock	;
       logic valid	;
       logic ready	;
			 logic done		;
				 
	div divisor(
				.valid	(	valid		),
				.ready	(	ready		),
				.clock	(	clock		),
				.nreset	(	nreset	),
				.a			(	num1		),
				.b			( 	num2	),
				.c			( 	out1	),
				.done		(		done	),
				.nclocks(	nclocks	)
	);
	parameter [31:0] N_testes = 1000;
	logic [31:0] mem [N_testes-1:0];
	logic [$clog2(N_testes)+1:0] next_test; 		
	logic [31:0] counter_done,pass;
       initial begin  	
									clock 	<= 0	;
       		        nreset 	<= 0	;
		      #2			nreset 	<= 1	;
		      
									for(integer i = 0; i < N_testes; i++)begin
										mem[i] = $urandom_range(1000,20);	  
									end			
       end

       logic state, next;
       always #1 clock = ~clock;

			 always_comb  num1 = mem[next_test+0];
			 always_comb	num2 = mem[next_test+1];
			 
			 always_ff@(posedge done, negedge nreset)begin
						if(!nreset)begin
							next_test <= 0;
							counter_done <=0;
							pass <= 0;
						end else begin		
							if(done)$display("%2d,	%2d,	%2d,	%2d,	%s %d",counter_done,mem[next_test+0],mem[next_test+1],mem[next_test]/mem[next_test+1],mem[next_test]/mem[next_test+1] == out1? "Pass": "Fail",nclocks);
							if(out1 == mem[next_test+1]/mem[next_test+1])pass <= pass +1;
							if(counter_done == N_testes/2)begin 
								$display("log");
								$display("total,	pass,	fail");
								$display("%d,	%d,	%d",N_testes/2,(pass/N_testes)*100,(1-pass/N_testes)*100);
								$finish;
							end
							next_test <= done ? next_test+2 : next_test;
							counter_done <= counter_done +1;
						end
			 end
       always_ff@(negedge clock, negedge nreset)
	       if(!nreset)  state <= 1;
	       else					state <= next;
					
       always_comb case(state)
				 0:begin
						next  = 1;
						valid = 0;
					end
				1:begin
					valid = 1;
					next = ready;
					end
       endcase
  endmodule 
