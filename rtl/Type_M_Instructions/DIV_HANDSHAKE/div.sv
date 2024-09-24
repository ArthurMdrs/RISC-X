// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         AUTHOR NAME AND EMAIL HERE                                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    DESIGN NAME HERE                                           //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    DESCRIPTION HERE.                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module div(	
		input logic 	       clock	,
		input logic 	       nreset	,
		input logic					 valid	,
		input logic 	[31:0] a			,
		input logic 	[31:0] b			,
		output logic 	[31:0] c			,
		output logic  [31:0] nclocks,	
		output logic				 ready	,
		output logic				 done	
);

	
	logic [31:0] quatient		;
	logic [31:0] remeinder	;
	logic	[31:0] a_internal	;
	logic [31:0] b_internal ;	
	enum {IDLE,START_LOAD, CALCULATION_LOOP, DONE} states;
	logic [31:0] state, next;
	always_comb a_internal  = (state == START_LOAD) ? a:a_internal;
	always_comb b_internal  = (state == START_LOAD) ? b:b_internal;
	always_comb c						= (state == DONE) ? quatient : c;
	always_comb done				=	(state == DONE);
	always_ff@(posedge clock, negedge nreset)begin
		if(!nreset) begin state <= IDLE	; nclocks <= 0;end
		else begin  state <= next	;
			    if(state == START_LOAD)begin
						quatient 	 <= 0;
						remeinder  <= a;
			    end else begin
				    	quatient 	<= next == DONE ? quatient : quatient +1;
							remeinder	<= next == DONE ? remeinder : remeinder -b;
							nclocks <= (state == CALCULATION_LOOP) ? nclocks + 1 :nclocks;
			    end

		end
	end	
	always_comb case(state)
		IDLE:begin
			next = valid ? START_LOAD : IDLE;
	end
		START_LOAD:begin
			ready = 1;
			next = a_internal < b_internal ? DONE : CALCULATION_LOOP;	
		end
		CALCULATION_LOOP:begin
			next = remeinder < b_internal ? DONE :CALCULATION_LOOP;
		end
		DONE:begin
			ready = 0;
			next = IDLE;
		end
  endcase
	
endmodule
