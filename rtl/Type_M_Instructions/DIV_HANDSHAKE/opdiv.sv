`include "./counter_bit.sv"
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
                .A      (a_reg),
                .nBits  (qbits),
                .mask   (mask)
    );
    enum {IDLE,INITIALISE_AND_COUNTER_BITS,SET_AK_MINUEND,LOOP,UPDATE_MINUEND_RIGHT,UPDATE_MINUEND_LEFT,INCREASE_K,DONE} states;
    always_ff@(negedge clock, negedge nreset)begin
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
    always_ff@(posedge clock, negedge nreset)begin
        if(!nreset)begin c <= 0;
                         c_signal <= 0;
        end
        else begin 
            case({a_signal,b_signal})
                  2'b10: c_signal <= 1;
                  2'b01: c_signal <= 1;
                default: c_signal <= 0;
            endcase
            c <= out_valid_o ? {c_signal,c_signal ? ~Quatient+1: Quatient}: c;
        end
    end
    always_comb left_updade     = {minuend,a_reg[next_k]};
    always_comb right_updade    = {minuend-b_reg,a_reg[next_k]};
    always_comb next_k          = k - 1;
    always_comb in_ready_o      = state == IDLE | state ==DONE;
    always_comb out_valid_o     = next==DONE;
endmodule