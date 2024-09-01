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