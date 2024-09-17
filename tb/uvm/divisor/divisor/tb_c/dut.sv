module opdiv(

    input  logic                 clock       ,
    input  logic                 nreset      ,
    input  logic  [31:0]   a           ,
    input  logic  [31:0]   b           ,
    output logic  [31:0]  c           ,
    input  logic                 in_valid_i  ,   //  
    output logic                in_ready_o  ,   //  
    output logic                out_valid_o ,   //  
    input  logic                 out_ready_i     // 
);

    logic ena, a_signal,b_signal, c_signal, next_in_ready_o, next_out_valid_o;
    logic [5:0] qbits;
    logic signed [31:0] state, next, k;
    logic [31:0] left_updade,right_updade;
    logic signed [31:0] Quatient,minuend,next_k,a_reg, b_reg;
    counter_bit inst0Count(
                .ena    (ena),
                .A      (a_reg[30:0]),
                .nBits  (qbits)
    );
    enum {IDLE,INITIALISE_AND_COUNTER_BITS,SET_AK_MINUEND,LOOP,UPDATE_MINUEND_RIGHT,UPDATE_MINUEND_LEFT,INCREASE_K,DONE} states;
    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset)begin
            a_reg       <= 0;
            b_reg       <= 0;
            Quatient    <= 0;
            state       <= IDLE;
            ena         <= 0;
            minuend     <= 0;
            a_signal    <= 0;
            b_signal    <= 0;
            in_ready_o <= 0;
            out_valid_o <= 0;
            k <= 0;
            in_ready_o <= 0;
        end else begin
            case(next)
                      INITIALISE_AND_COUNTER_BITS:
                begin
                        Quatient    <= 0;
                        a_reg       <= a;//{1'b0,a[30:0]}; ok
                        b_reg       <= b;//{1'b0,b[30:0]};
                        ena         <= 1;
                        minuend     <= 0;
                        k           <= qbits;     
                        a_signal    <= a[31];
                        b_signal    <= b[31];                             
                end
                SET_AK_MINUEND:
                begin  
                        minuend     <= 1;
                        ena         <= 0;
                        Quatient    <= 0;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        k           <= qbits; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                end
                LOOP:
                begin  
                    if(minuend - b_reg >= 0)begin
                        Quatient[k] <= 1;
                        ena         <= 0;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        k           <= k;    
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;                  
                    end else begin
                        ena         <= ena;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient[k] <= 0;
                        k           <= k;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                    end      
                end
                UPDATE_MINUEND_RIGHT:
                begin
                        ena         <= ena;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient    <= Quatient;
                        k           <= k;
                        minuend     <= right_updade; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;       
                end
                INCREASE_K:
                begin 
                        k           <= next_k;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        minuend     <= minuend;
                        ena         <= ena;
                        Quatient    <= Quatient;       
                         a_signal    <= a_signal;
                        b_signal    <= b_signal;        
                end
                UPDATE_MINUEND_LEFT:
                begin
                        minuend     <= left_updade;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;      
                end
                DONE:
                begin
                        minuend     <= minuend;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                end
                default:
                begin
                        a_reg       <= 0;
                        b_reg       <= 0;
                        Quatient    <= 0;
                        state       <= 0;
                        ena         <= 0;
                        minuend     <= 0;
                        k           <= 0; 
                        a_signal    <= 0;
                        b_signal    <= 0;  
                end            
            endcase
            state <= next;
            in_ready_o  <= next_in_ready_o;
            out_valid_o <= next_out_valid_o;
        end
    end


    always_comb case(state) 
        IDLE                        :                           {next,next_in_ready_o,next_out_valid_o} = in_valid_i && in_ready_o  ? {INITIALISE_AND_COUNTER_BITS,2'b00}:{IDLE,2'b10}  ;
        INITIALISE_AND_COUNTER_BITS :                           {next,next_in_ready_o,next_out_valid_o} = {SET_AK_MINUEND,2'b00}                                                        ;
        SET_AK_MINUEND              :                           {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        LOOP                        :begin 
                                     if((minuend - b_reg) >= 0) {next,next_in_ready_o,next_out_valid_o} = (!k) ? {DONE,2'b01} : {UPDATE_MINUEND_RIGHT,2'b00}                            ;
                                     else                       {next,next_in_ready_o,next_out_valid_o} = (!k )? {DONE,2'b01} : {UPDATE_MINUEND_LEFT ,2'b00 }                           ;  
                                     end
        UPDATE_MINUEND_RIGHT        :                           {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        UPDATE_MINUEND_LEFT         :                           {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        INCREASE_K                  :                           {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        DONE                        :begin 

                                     if(!out_ready_i)           {next,next_in_ready_o,next_out_valid_o} = {DONE,2'b01}                                                                  ;
                                     else                       {next,next_in_ready_o,next_out_valid_o} = {IDLE,2'b10}                                                  ;
                                     end
        default                     :next = IDLE;
    endcase

    always_comb c = out_valid_o && out_ready_i ?  Quatient[30:0]: 'x;
    always_comb left_updade     = {minuend,a_reg[next_k]};
    always_comb right_updade    = {minuend-b_reg,a_reg[next_k]};
    always_comb next_k          = k - 1;

endmodule


/*
module opdiv(

    input  logic                 clock       ,
    input  logic                 nreset      ,
    input  logic signed [31:0]   a           ,
    input  logic signed [31:0]   b           ,
    output logic signed [31:0]  c           ,
    input  logic                 in_valid_i  ,   //  
    output logic                in_ready_o  ,   //  
    output logic                out_valid_o ,   //  
    input  logic                 out_ready_i     // 
);

    logic ena, a_signal,b_signal, c_signal, next_in_ready_o, next_out_valid_o;
    logic [5:0] qbits;
    logic signed [31:0] state, next, k;
    logic [31:0] left_updade,right_updade;
    logic signed [31:0] Quatient,minuend,next_k,a_reg, b_reg;
    counter_bit inst0Count(
                .ena    (ena),
                .A      (a_reg[30:0]),
                .nBits  (qbits)
    );
    enum {IDLE,INITIALISE_AND_COUNTER_BITS,SET_AK_MINUEND,LOOP,UPDATE_MINUEND_RIGHT,UPDATE_MINUEND_LEFT,INCREASE_K,DONE} states;
    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset)begin
            a_reg       <= 0;
            b_reg       <= 0;
            Quatient    <= 0;
            state       <= IDLE;
            ena         <= 0;
            minuend     <= 0;
            a_signal    <= 0;
            b_signal    <= 0;
            in_ready_o <= 0;
            out_valid_o <= 0;
            k <= 0;
            in_ready_o <= 0;
        end else begin
            case(next)
                      INITIALISE_AND_COUNTER_BITS:
                begin
                        Quatient    <= 0;
                        a_reg       <= a;//{1'b0,a[30:0]}; ok
                        b_reg       <= b;//{1'b0,b[30:0]};
                        ena         <= 1;
                        minuend     <= 0;
                        k           <= qbits;     
                        a_signal    <= a[31];
                        b_signal    <= b[31];                             
                end
                SET_AK_MINUEND:
                begin  
                        minuend     <= 1;
                        ena         <= 0;
                        Quatient    <= 0;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        k           <= qbits; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                end
                LOOP:
                begin  
                    if(minuend - b_reg >= 0)begin
                        Quatient[k] <= 1;
                        ena         <= 0;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        k           <= k;    
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;                  
                    end else begin
                        ena         <= ena;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient[k] <= 0;
                        k           <= k;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                    end      
                end
                UPDATE_MINUEND_RIGHT:
                begin
                        ena         <= ena;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient    <= Quatient;
                        k           <= k;
                        minuend     <= right_updade; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;       
                end
                INCREASE_K:
                begin 
                        k           <= next_k;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        minuend     <= minuend;
                        ena         <= ena;
                        Quatient    <= Quatient;       
                         a_signal    <= a_signal;
                        b_signal    <= b_signal;        
                end
                UPDATE_MINUEND_LEFT:
                begin
                        minuend     <= left_updade;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;      
                end
                DONE:
                begin
                        minuend     <= minuend;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                end
                default:
                begin
                        a_reg       <= 0;
                        b_reg       <= 0;
                        Quatient    <= 0;
                        state       <= 0;
                        ena         <= 0;
                        minuend     <= 0;
                        k           <= 0; 
                        a_signal    <= 0;
                        b_signal    <= 0;  
                end            
            endcase
            state <= next;
            in_ready_o  <= next_in_ready_o;
            out_valid_o <= next_out_valid_o;
        end
    end


    always_comb case(state) 
        IDLE                        :                           {next,next_in_ready_o,next_out_valid_o} = in_valid_i ? {INITIALISE_AND_COUNTER_BITS,2'b00}:{IDLE,2'b10}                 ;
        INITIALISE_AND_COUNTER_BITS :                           {next,next_in_ready_o,next_out_valid_o} = {SET_AK_MINUEND,2'b00}                                                        ;
        SET_AK_MINUEND              :                           {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        LOOP                        :begin 
                                     if((minuend - b_reg) >= 0) {next,next_in_ready_o,next_out_valid_o} = (!k) ? {DONE,2'b01} : {UPDATE_MINUEND_RIGHT,2'b00}                            ;
                                     else                       {next,next_in_ready_o,next_out_valid_o} = (!k )? {DONE,2'b01} : {UPDATE_MINUEND_LEFT ,2'b00 }                           ;  
                                     end
        UPDATE_MINUEND_RIGHT        :                           {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        UPDATE_MINUEND_LEFT         :                           {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        INCREASE_K                  :                           {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        DONE                        :begin 

                                     if(!out_ready_i)           {next,next_in_ready_o,next_out_valid_o} = {DONE,2'b01}                                                                  ;
                                     else                       {next,next_in_ready_o,next_out_valid_o} = {IDLE,2'b10}                                                  ;
                                     end
        default                     :next = IDLE;
    endcase

    always_comb c = out_valid_o && out_ready_i ?  Quatient[30:0]: 'x;
    always_comb left_updade     = {minuend,a_reg[next_k]};
    always_comb right_updade    = {minuend-b_reg,a_reg[next_k]};
    always_comb next_k          = k - 1;

endmodule

// out_valid_o  = next == DONE && in_ready_o 

*/

/*
module opdiv(

    input logic                 clock       ,
    input logic                 nreset      ,
    input logic signed [31:0]   a           ,
    input logic signed [31:0]   b           ,
    output logic signed [31:0]  c           ,
    input logic                 in_valid_i  ,   //  dado válido
    output logic                in_ready_o  ,   //  início do cálculo
    output logic                out_valid_o ,   //  cálculo finalizado
    input logic                 out_ready_i     //  dado coletado
);

    logic ena, a_signal,b_signal, c_signal;
    logic [5:0] qbits;
    logic signed [30:0] a_reg, b_reg, Quatient, state, next, minuend, k, mask;
    logic signed [30:0] left_updade,right_updade,next_k;
    counter_bit inst0Count(
                .ena    (ena),
                .a      (a_reg),
                .nBits  (qbits),
                .mask   (mask)
    );
    enum {IDLE,INITIALISE_AND_COUNTER_BITS,SET_AK_MINUEND,LOOP,UPDATE_MINUEND_RIGHT,UPDATE_MINUEND_LEFT,INCREASE_K,DONE} states;
    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset)begin
            a_reg       <= 0;
            b_reg       <= 0;
            Quatient    <= 0;
            state       <= IDLE;
            ena         <= 0;
            minuend     <= 0;
            a_signal    <= 0;
            b_signal    <= 0;
            k <= 0;
        end else begin
            case(next)
                IDLE:
                begin
                        a_reg       <= 0;
                        b_reg       <= 0;
                        ena         <= 0;
                        Quatient    <= 0;
                        minuend     <= 0;
                        a_signal    <= 0;
                        b_signal    <= 0;   
                        k           <= qbits;            
                end        
                INITIALISE_AND_COUNTER_BITS:
                begin
                        Quatient    <= 0;
                        a_reg       <= a[31] ? ~a[30:0] + 1 :a[30:0];
                        b_reg       <= b[31] ? ~b[30:0] + 1 :b[30:0];
                        a_signal    <= a[31];
                        b_signal    <= b[31];
                        ena         <= 1;
                        minuend     <= 0;
                        k           <= qbits;                                  
                end
                SET_AK_MINUEND:
                begin  
                        minuend     <= 1;
                        ena         <= 0;
                        Quatient    <= 0;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        k           <= qbits;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;    
                end
                LOOP:
                begin  
                    if(minuend - b_reg >= 0)begin
                        Quatient[k] <= 1;
                        ena         <= 0;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        k           <= k;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;                        
                    end else begin
                        ena         <= ena;
                        minuend     <= minuend;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient[k] <= 0;
                        k           <= k;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;
                    end      
                end
                UPDATE_MINUEND_RIGHT:
                begin
                        ena         <= ena;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        Quatient    <= Quatient;
                        k           <= k;
                        minuend     <= right_updade;  
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;       
                end
                INCREASE_K:
                begin 
                        k           <= next_k;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;
                        minuend     <= minuend;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;       
        
                end
                UPDATE_MINUEND_LEFT:
                begin
                        minuend     <= left_updade;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg;   
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;     
                end
                DONE:
                begin
                        minuend     <= minuend;
                        k           <= k;
                        ena         <= ena;
                        Quatient    <= Quatient;
                        a_reg       <= a_reg;
                        b_reg       <= b_reg; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal;   
                end
                default:
                begin
                        a_reg       <= 0;
                        b_reg       <= 0;
                        Quatient    <= 0;
                        state       <= 0;
                        ena         <= 0;
                        minuend     <= 0;
                        k           <= 0; 
                        a_signal    <= a_signal;
                        b_signal    <= b_signal; 
                end            
            endcase
            state <= next;
        end
    end


    always_comb case(state) 
        IDLE                        :next = in_valid_i ? INITIALISE_AND_COUNTER_BITS:   IDLE                    ;
        INITIALISE_AND_COUNTER_BITS :next = SET_AK_MINUEND                                                      ;
        SET_AK_MINUEND              :next = LOOP                                                                ;
        LOOP                        :begin 
                                     if(minuend - b_reg >= 0) next = k == 0 ? DONE : UPDATE_MINUEND_RIGHT       ;
                                     else                     next = k == 0 ? DONE : UPDATE_MINUEND_LEFT        ;  
                                    end
        UPDATE_MINUEND_RIGHT        :next = INCREASE_K                                                          ;
        UPDATE_MINUEND_LEFT         :next = INCREASE_K                                                          ;
        INCREASE_K                  :next = LOOP                                                                ;
        DONE                        :begin next = IDLE                                                          ;
                                     if(!out_ready_i) next = DONE                                               ;
                                     else             next = in_valid_i ? INITIALISE_AND_COUNTER_BITS : IDLE    ;
        end
        default                     :next = IDLE;
    endcase

    always_comb c_signal        = a_signal == b_signal ? 0 : 1;
    always_comb c <= out_valid_o ? {c_signal,c_signal ? ~Quatient+1: Quatient}: c;
    always_comb left_updade     = {minuend,a_reg[next_k]};
    always_comb right_updade    = {minuend-b_reg,a_reg[next_k]};
    always_comb next_k          = k - 1;
    always_comb in_ready_o      = state == IDLE | state ==DONE;
    always_comb out_valid_o     = next==DONE;
endmodule
*/

/*
module div( 
        input  logic                clock        ,
        input  logic                nreset       ,
        input  logic                in_valid_i   , //data valid     in_valid (input)
        output logic                in_ready_o   , //start calcule  in_ready (output)
        input  logic signed  [31:0] a            ,
        input  logic signed  [31:0] b            ,
        output logic signed  [31:0] c            ,
        output logic         [31:0] nclocks      , 
        output logic                out_valid_o  , //finished calcule   out_valid (output)
        input  logic                out_ready_i    //data ready	        out_ready (input)
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
*/

/*
module div( 
  input logic            clock        ,
  input logic            nreset       ,
  input logic            in_valid_i   , //in
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
//always_comb out_valid_o = done              ;

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
      //in_ready_o = 1;
      out_valid_o = 1;
  end
endcase
endmodule
*/