module div(	
		input logic 	clock	, //Signal Clock
		input logic 	nreset	, //Reset low signal
		input logic	valid	, //Data is valid?
		input logic 	[31:0] a, //Dividendo
		input logic 	[31:0] b, //Divisor
		output logic 	[31:0] c, //Resultado
		output logic    [31:0] nclocks,	// Numbers for cycles on the operation
		output logic    ready	, //Detecção de dado em barramento
		output logic    done	  //Conclusion operation
);

//Variables internals
	logic [31:0] quatient; 		//Quociente = resultado
	logic [31:0] remeinder;		//Resto 		
	logic [31:0] a_internal;	
	logic [31:0] b_internal;	

	enum {
		 IDLE,
		 START_LOAD, 
		 CALCULATION_LOOP, 
		 DONE
		 } states;

	logic [31:0] state, next;

// Syncronus Logic - Update Registers

	always_ff@(posedge clock, negedge nreset)begin
		if(!nreset) begin 
			state <= IDLE	; nclocks <= 0;
		end
		else begin  
			state <= next	;
			if(state == START_LOAD)begin
				quatient    <= 0;
			        remeinder   <= a;
			end 
			else begin
				//Enquanto o resto não for menor que o divisor some mais 1
				quatient  <= (next == DONE) ? quatient : quatient +1;
				//Enquanto o resto não for menor que o divisor subtraia pelo divisor
				remeinder <= (next == DONE) ? remeinder : remeinder -b;
				nclocks   <= (state == CALCULATION_LOOP) ? nclocks + 1 :nclocks;
			    end
		end
	end	

//Next-state Logic

	always_comb case(state)
		IDLE:begin
			next = valid ? START_LOAD : IDLE;
		end
		START_LOAD:begin
			ready = 1;
			//Se dividendo for menor que o divisor - fim 
			next = a_internal < b_internal ? DONE : CALCULATION_LOOP;	
		end
		CALCULATION_LOOP:begin
			//Se o resto for menor que o divisor - fim
			next = remeinder < b_internal ? DONE :CALCULATION_LOOP;
		end
		DONE:begin
			ready = 0;
			next = IDLE;
		end
  endcase

//Output Logic

	always_comb a_internal  = (state == START_LOAD) ? a:a_internal;
	always_comb b_internal  = (state == START_LOAD) ? b:b_internal;
	//If state = done -> Result or data c?
	always_comb c	        = (state == DONE) ? quatient : c;
	
	always_comb done	= (state == DONE);

	
endmodule


