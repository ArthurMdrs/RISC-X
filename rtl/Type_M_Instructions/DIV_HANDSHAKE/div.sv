module div( 
        input  logic                clock        ,
        input  logic                nreset       ,
        input  logic                in_valid_i   ,
        output logic                in_ready_o   ,
        input  logic signed  [31:0] a            ,
        input  logic signed  [31:0] b            ,
        output logic signed  [31:0] c           ,
        output logic         [31:0] nclocks     , 
        output logic                out_valid_o  ,
        input  logic                out_ready_i  	 
);
    
    logic [30:0] quatient   ;
    logic [30:0] remeinder  ;
    logic [30:0] a_internal ;
    logic [30:0] b_internal ;
    logic        a_signal   ;
    logic        b_signal   ;   
    logic        c_signal   ;

    enum {IDLE,START_LOAD, CALCULATION_LOOP, DONE} stateCurrents;
    logic [31:0] stateCurrent, nextState                                                ;
    always_comb out_valid_o =   (stateCurrent == DONE)                                  ;
    always_comb c           =   {c_signal,c_signal ? ~quatient+1 :quatient}             ;
    always_comb in_ready_o = stateCurrent == IDLE | stateCurrent == DONE; 
    always_comb case({a_signal,b_signal})
                2'b10   :c_signal = 1;
                2'b01   :c_signal = 1;
                default :c_signal = 0;
    endcase
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
                        remeinder   <= a[31] ? ~a[30:0]+1:a[30:0];
                        a_internal  <= a[31] ? ~a[30:0]+1:a[30:0];
                        b_internal  <= b[31] ? ~b[30:0]+1:b[30:0];
                        a_signal    <= a[31]    ;
                        b_signal    <= b[31]    ;
                end else begin
                        quatient    <= nextState == DONE ?                  quatient  : quatient + 1            ;
                        remeinder   <= nextState == DONE ?               remeinder    : remeinder - b_internal  ;
                        nclocks     <= nextState == CALCULATION_LOOP ?   nclocks + 1  : 0                       ;          
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
