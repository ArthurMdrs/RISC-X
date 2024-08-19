/*
    Arquivo para implementação da interface OBI

    Criado por: Túlio Tavares e Victor Hugo
    Data: 14/08/2024


    Ultima modificação: 19/08/2024
    Descrição: Alterações de Padrão de nomes;
    Autores: Túlio Tavares e Victor Hugo

*/

// uma lógica possível está encaminhada
// confira o funcionamento, mas considere as ressalvas que:
//     - as entradas e saídas ainda não estão completamente definidas ou dentro da sintaxe
//     - nas linhas [47] e [87 : 108] temos lógica ainda indefinida
// quero ainda discutir a linha [124]

module OBI_controler #(
    parameter WIDTH = 32
) (

    input clk,                  // CLOCK DO CORE
    input rst_n,                // RESET NA BORDA NEGATIVA

    // PINOS DO CORE
    input addr_c_i,             // ENDEREÇO
    input we_c_i,               // ESCREVE OU LÊ?
    input wdata_c_i,            // DADO QUE VAI SER ESCRTIO
    input mem_data_type_i,      // TIPO DE DADO
    input req_c_i               // REQUISIÇÃO DE NOVA OPERAÇÃO

    // PINOS DA MEMORIA
    input gnt_m_i,              // ESTÁ PRONTA PARA UM OPERAÇÃO
    input rvalid_m_i,           // O DADO REQUISITADO ESTÁ PRONTO
    input rdata_m_i,            // DADO QUE FOI LIDO

    // PINOS DE CONTROLE DO OBI - DESTINADOS A MEMÓRIA
    output req_m_o,             // INDICA QUE TEM UMA OPERAÇÃO A SER FEITA
    output addr_m_o,            // ENDEREÇO VÁLIDO PARA A OPERAÇÃO
    output we_m_o,              // INDICA SE A OPERAÇÃO É DE ESCRITA OU LEITURA
    output be_m_o,              // INDICA QUAIS BYTES SERÃO LIDOS
    output wdata_m_o,           // DADO QUE VAI SER ENVIADO A MEMÓRIA

    // PINOS SOB CONTROLE DO OBI - DESTINADOS AO CORE
    output rdata_c_o,           // DADO PRONTO PARA SER ACESSADO
    output rvalid_c_o           // OPERAÇÃO DE LEITURA/ESCRITA CONCLUÍDA

);

    OBI_state_t state, next_state;     

    logic [31:0]        addr_nxt, wdata_nxt;
    immediate_source_t  mem_data_type_nxt;
    logic               we_nxt;

    always_ff(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            addr_nxt            = 0;
            we_nxt              = 0;
            mem_data_type_nxt   = 0;
            wdata_nxt           = 0;
            state               = IDLE;
        end
        else begin
            case (state)
                IDLE: begin
                    if (req_c_i) begin       // se não tiver nenhuma operação na fila e o core solicitar uma,
                                                        // ele salva os dados e vai para o próximo passo
                        addr_nxt            = addr_c_i;
                        we_nxt              = we_c_i;
                        wdata_nxt           = wdata_c_i;
                        mem_data_type_nxt   = mem_data_type_i;

                        state = next_state;    
                    end
                end
                REQUESTING: begin
                    if (gnt_m_i && req_c_i)
                        state = next_state;
                    
                    if(~req_c_i)
                        state = IDLE;
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
                req_m_o = 0;
                //i_valid = 1;
                rvalid_c_o = 0;
            end
            REQUESTING: begin
                next_state = WAITING;
                req_m_o     = 1;
                //i_valid = 0;
                rvalid_c_o = 0;

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
                req_m_o     = 0;
                //i_valid = 0;
                rvalid_c_o = 0;
            end
            DUMPING:    begin
                next_state = IDLE;
                req_m_o     = 0;
                //i_valid = 0;
                rvalid_c_o = 1;

                if (we_nxt) // podemos colocar ou não essa condição
                    data_out = rdata;
            end
            default: 
                next_state = IDLE;
        endcase
    end

endmodule