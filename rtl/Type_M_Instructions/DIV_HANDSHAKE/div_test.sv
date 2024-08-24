`include "./div.sv"
module tb();
		parameter [31:0] numero_de_testes = 2;
		logic 			clock		;
		logic 			nreset		;
		logic 			in_valid_i	;
		logic 			in_ready_o	;
		logic   [31:0]	a			;
		logic 	[31:0]	b			;
		logic 	[31:0]	c			;
		logic 			out_valid_o	;
		logic			out_ready_i	;
		logic 	[31:0]	nclocks		;
		div divisor(
		
				.clock		(	clock		),	
				.nreset		(	nreset		),
				.in_valid_i	(	in_valid_i	),
				.in_ready_o	(	in_ready_o	),
				.a			(	a			),
				.b			(	b			),
				.c			(	c			),
				.out_valid_o(	out_valid_o	),
				.out_ready_i(	out_ready_i	),
				.nclocks	(	nclocks		)	
		
		);

		initial begin 
			clock 		= 	0	;
			in_valid_i 	= 	0	;

		#1 	nreset 		= 	1	;
		#1  nreset 		= 	0	;
		#1	nreset 		= 	1	;
		#1
			in_valid_i = 	1	;
		end
		always#3 clock = ~clock;

		logic [31:0] counter1,counter2,temp;
		always_ff@(posedge clock,negedge nreset) 
			if(!nreset) begin
				out_ready_i <= 		0	;	
				counter1 	<= 		0	;
				counter2 	<= 		0	;
				temp  		<= $urandom_range(10,1);
				a 			<=		100	;
				b 			<=		5	;

			end
			else if(out_valid_o) 
			begin
				if(counter2 <= numero_de_testes)begin
					if(counter1 <= temp)counter1 <= counter1 + 1;
					else begin
						out_ready_i <=	1 					;
						a 			<=	$urandom_range(100,1);
						b 			<=	$urandom_range(10,1);	
						counter1 	<= 	0					;
						counter2 	<= counter2 + 1			;
						temp  		<= $urandom_range(10,1)	;
					end
				end
				else
					$finish;
			end

endmodule
