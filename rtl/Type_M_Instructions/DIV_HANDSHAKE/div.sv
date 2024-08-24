module div( 
        input  logic            clock        ,
        input  logic            nreset       ,
        input  logic            in_valid_i   ,
        output logic            in_ready_o   ,
        input  logic     [31:0] a            ,
        input  logic     [31:0] b            ,
        output logic     [31:0]  c           ,
        output logic     [31:0]  nclocks     , 
        output logic            out_valid_o  ,
        input  logic            out_ready_i  	 
);
    
    logic [31:0] quatient   ;
    logic [31:0] remeinder  ;
    logic [31:0] a_internal ;
    logic [31:0] b_internal ;   
    enum {IDLE,START_LOAD, CALCULATION_LOOP, DONE} stateCurrents;
    logic [31:0] stateCurrent, nextState                        ;
    always_comb out_valid_o =   (stateCurrent == DONE)          ;
    always_comb c           =   quatient                        ;
    always_comb in_ready_o = stateCurrent == IDLE | stateCurrent == DONE; 
    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset) begin 
            stateCurrent    <= IDLE ; 
            nclocks         <= 0;
            quatient        <= 0;
            a_internal      <= 0;
            b_internal      <= 0;
            remeinder       <= 0;
        end
        else begin  stateCurrent <= nextState;
                if(stateCurrent == START_LOAD)begin
                        quatient    <= 0;
                        remeinder   <= a;
                        a_internal  <= a;
                        b_internal  <= b;
                end else begin
                        quatient    <= nextState == DONE ? quatient  : quatient + 1;
                        remeinder   <= nextState == DONE ? remeinder : remeinder - b_internal;
                        nclocks     <= (nextState == CALCULATION_LOOP) ? nclocks + 1 :0;
                end
        end
    end 

    always_comb case(stateCurrent)
        IDLE:begin
            nextState = in_valid_i ? START_LOAD : IDLE;
        end
        START_LOAD:begin
            nextState = CALCULATION_LOOP;   
        end
        CALCULATION_LOOP:begin
            nextState = remeinder < b_internal ? DONE :CALCULATION_LOOP;
        end
        DONE:begin
            if(!out_ready_i) nextState = DONE;
            else             nextState = in_valid_i ? START_LOAD : IDLE;
        end
  endcase
endmodule
