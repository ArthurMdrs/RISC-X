
module opdiv(
    input  logic                clock           ,
    input  logic                nreset          ,
    input  logic signed [31:0]  a               ,
    input  logic signed [31:0]  b               ,
    output logic signed [31:0]  c               ,
    input  logic                in_valid_i      ,   //  
    output logic                in_ready_o      ,   //  
    output logic                out_valid_o     ,   //  
//    input logic                 signal_division ,
    input  logic                out_ready_i     // 
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
            in_ready_o  <= 0;
            out_valid_o <= 0;
            k           <= 0;
            in_ready_o  <= 0;
        end else begin
            case(next)
                INITIALISE_AND_COUNTER_BITS:
                begin
                        Quatient    <= 0;
                        a_reg[30:0] <= a[31] ? {1'b0,~a[30:0]+1}: a[30:0];
                        b_reg[30:0] <= b[31] ? {1'b0,~b[30:0]+1}: b[30:0];
                        ena         <= 1;
                        minuend     <= 0;
                        k           <= qbits;     
                        a_signal    <= a[31];
                        b_signal    <= b[31];    
                        a_reg[31]   <= 0;
                        b_reg[31]   <= 0;                         
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
        IDLE                        :                               {next,next_in_ready_o,next_out_valid_o} = (in_valid_i && in_ready_o) ? {INITIALISE_AND_COUNTER_BITS,2'b00}:{IDLE,2'b10} ;
        INITIALISE_AND_COUNTER_BITS :                               {next,next_in_ready_o,next_out_valid_o} = {SET_AK_MINUEND,2'b00}                                                        ;
        SET_AK_MINUEND              :                               {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        LOOP                        :begin 
                                        if((minuend - b_reg) >= 0)  {next,next_in_ready_o,next_out_valid_o} = (!k) ? {DONE,2'b01} : {UPDATE_MINUEND_RIGHT,2'b00}                            ;
                                        else                        {next,next_in_ready_o,next_out_valid_o} = (!k )? {DONE,2'b01} : {UPDATE_MINUEND_LEFT ,2'b00 }                           ;  
                                    end
        UPDATE_MINUEND_RIGHT        :                               {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        UPDATE_MINUEND_LEFT         :                               {next,next_in_ready_o,next_out_valid_o} = {INCREASE_K,2'b00}                                                            ;
        INCREASE_K                  :                               {next,next_in_ready_o,next_out_valid_o} = {LOOP,2'b00}                                                                  ;
        DONE                        :begin 

                                     if(!out_ready_i)               {next,next_in_ready_o,next_out_valid_o} = {DONE,2'b01}                                                                  ;
                                     else                           {next,next_in_ready_o,next_out_valid_o} = {IDLE,2'b10}                                                  ;
                                     end
        default                     :next = IDLE;
    endcase

    //always_comb c = out_valid_o && out_ready_i ?  Quatient[30:0]: 'x;
    always_comb 
        if(out_valid_o && out_ready_i)
            if(b_reg[30:0] == 0)
                c = {31{1'b1}};
            else if(a_reg[30:0] == 0)
                c = {31{1'b0}};
            else  
                case({a_signal,b_signal})
                    2'b00: c = {1'b0,Quatient[30:0]};
                    2'b11: c = {1'b0,Quatient[30:0]};
                    2'b10: c = {1'b1,~Quatient[30:0]+1};
                    2'b01: c = {1'b1,~Quatient[30:0]+1};
                endcase
        else
            c = 'x;


    always_comb left_updade     = {minuend,a_reg[next_k]};
    always_comb right_updade    = {minuend-b_reg,a_reg[next_k]};
    always_comb next_k          = k - 1;

endmodule

// out_valid_o  = next == DONE && in_ready_o 