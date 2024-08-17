// uma lógica possível está encaminhada
// confira o funcionamento, mas considere as ressalvas que:
//     - as entradas e saídas ainda não estão completamente definidas ou dentro da sintaxe
//     - nas linhas [47] e [87 : 108] temos lógica ainda indefinida
// quero ainda discutir a linha [124]

module OBI_controler #(
    parameter WIDTH = 32
) (
    OBI_if.MANAGER master
);
    /*
    modport MANAGER(
        output req,
        output addr,
        output we,
        output be,
        output wdata,
        input gnt,
        input rvalid,
        input rdata
    );
    */
    //input addr_in, we_in
    //input mem_data_type_i
    //output i_valid, o_valid, data_out 
    
    typedef enum logic [2:0] {IDLE, REQUESTING, WAITING, DUMPING} state_type;
    state_type state, next_state;     

    logic [31:0]        addr_nxt, wdata_nxt;
    immediate_source_t  mem_data_type_nxt;
    logic               we_nxt;


    always_ff(posedge clk or posedge rst) begin
        if (rst) begin
            addr_nxt            = 0;
            we_nxt              = 0;
            mem_data_type_nxt   = 0;
            wdata_nxt           = 0;
            state               = IDLE;
        end
        else begin
            case (state)
                IDLE: begin
                    if (variavel_a_definir) begin       // se não tiver nenhuma operação na fila e o core solicitar uma,
                                                        // ele salva os dados e vai para o próximo passo
                        addr_nxt            = addr_in;
                        we_nxt              = we_in;
                        wdata_nxt           = wdata_in;
                        mem_data_type_nxt   = mem_data_type_i;

                        state = next_state;    
                    end
                end
                REQUESTING: begin
                    if (gnt)
                        state = next_state;
                end
                WAITING: begin
                    if (rvalid)
                        state = next_state;
                end
                DUMPING: begin
                        state = next_state;
                end
            endcase
        end
    end

    always_comb begin
        case(state)
            IDLE:       begin
                next_state = REQUESTING;
                req     = 0;
                i_valid = 1;
                o_valid = 0;
            end
            REQUESTING: begin
                next_state = WAITING;
                req     = 1;
                i_valid = 0;
                o_valid = 0;

                // é necessário revisão/discussão a respeito do endereçamento da memória
                case(mem_data_type_nxt)
                    WORD:           be = 4'b1111;
                    HALF_WORD: begin
                        if (addr_nxt[4] == 1)
                                    be = 4'b1100;
                        else
                                    be = 4'b0011;
                    end
                    BYTE: begin
                        case (addr_nxt[4:3])
                        2'd3:       be = 4'b1000;
                        2'd2:       be = 4'b0100;
                        2'd1:       be = 4'b0010;
                        2'd0:       be = 4'b0001;
                        default:    be = 0;
                        endcase
                    end
                    default:        be = 0;
                endcase

                //addr  = {addr_nxt[31:5], 5'b0);  
                addr    = addr_nxt;
                we      = we_nxt;
                wdata   = wdata_nxt;
            end
            WAITING:    begin
                next_state = DUMPING;
                req     = 0;
                i_valid = 0;
                o_valid = 0;
            end
            DUMPING:    begin
                next_state = IDLE;
                req     = 0;
                i_valid = 0;
                o_valid = 1;

                if (we_nxt) // podemos colocar ou não essa condição
                    data_out = rdata;
            end
            default: 
                next_state = IDLE;
        endcase

    end


endmodule