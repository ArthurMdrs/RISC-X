module div( 
        input logic            clock        ,
        input logic            nreset       ,
        input logic            in_valid_i   ,
        output logic           in_ready_o   ,
        input logic     [31:0] a            ,
        input logic     [31:0] b            ,
        output logic    [31:0] c            ,
        output logic    [31:0] nclocks, 
        output logic           out_valid_o  ,
        input logic            out_ready_i  ,
        output logic           done 
);

    logic [31:0] quatient       ;
    logic [31:0] remeinder  ;
    logic [31:0] a_internal ;
    logic [31:0] b_internal ;   
    enum {IDLE,START_LOAD, CALCULATION_LOOP, DONE} states;
    logic [31:0] state, next;
    always_comb done        =(state == DONE)    ;
    always_comb c           = quatient          ;
    always_comb out_valid_o = done              ;

    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset) begin state <= IDLE ; nclocks <= 0;end
        else begin  state <= next;
                if(state == START_LOAD)begin
                        quatient    <= 0;
                        remeinder   <= a_internal;
                        a_internal  <= a;
                        b_internal  <= b;
    
                end else begin
                        quatient    <= next == DONE ? quatient  : quatient + 1;
                        remeinder   <= next == DONE ? remeinder : remeinder - b_internal;
                        nclocks      <= (state == CALCULATION_LOOP) ? nclocks + 1 :0;
                end

        end
    end 

    always_comb case(state)
        IDLE:begin
            next = in_valid_i ? START_LOAD : IDLE;
            in_ready_o = 1;
        end
        START_LOAD:begin
            in_ready_o = 0;
            next = a_internal < b_internal ? DONE : CALCULATION_LOOP;   
        end
        CALCULATION_LOOP:begin
            next = remeinder < b_internal ? DONE :CALCULATION_LOOP;
            in_ready_o = 0;
        end
        DONE:begin
            if(!out_ready_i) next = DONE;
            else             next = in_valid_i ? START_LOAD : IDLE;
            in_ready_o = 1;
        end
  endcase
endmodule
