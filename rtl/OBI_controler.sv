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

module OBI_controler_if #(
    parameter WIDTH = 32
) (
    
    input logic                 clk,
    input logic                 rst_n,

    // Transaction request interface
    input  logic                core_valid_i,
    output logic                core_ready_o,
    input  logic [WIDTH-1:0]    core_addr_i,
    input  logic                core_we_i,
    input  logic [3:0]          core_be_i,
    input  logic [WIDTH-1:0]    core_wdata_i,

    // Transaction response interface
    output logic                resp_valid_o,  // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
    output logic [WIDTH-1:0]    resp_rdata_o,
    output logic                resp_err_o,

    // OBI interface
    output logic                obi_req_o,
    input  logic                obi_gnt_i,
    output logic [WIDTH-1:0]    obi_addr_o,
    output logic                obi_we_o,
    output logic [ 3:0]         obi_be_o,
    output logic [WIDTH-1:0]    obi_wdata_o,
    output logic [ 5:0]         obi_atop_o,
    input  logic [WIDTH-1:0]    obi_rdata_i,
    input  logic                obi_rvalid_i
    input  logic                obi_err_i

);

    OBI_state_t                 state, next_state;     

    // Internal Registers (TODO)
    
        // core to mem
            logic [WIDTH-1:0]    addr_aux_i;
            logic                we_aux_i;
            logic [3:0]          be_aux_i;
            logic [WIDTH-1:0]    wdata_aux_i;

        // mem to core
            logic [WIDTH-1:0]    rdata_aux_i;

    // Assigns 

        assign resp_valid_o = obi_rvalid_i;

    always_ff(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            obi_addr_o          = 32'b0;
            obi_we_o            = 0;
            obi_be_o            = 4'b0;
            obi_wdata_o         = 32'b0;
            state               = IDLE;
        end
        else begin
            case (state)

                /*
                IDLE: Aguarda o sinal do core que indica que o sinal de endereço e dado a ser enviado
                é válido, quando isso ocorrer os dados serão guardados em registradores e o obi_req_o 
                deve subir. Após tudo isso o bloco vai para próximo estado.
                */

                IDLE: begin
                    if (core_valid_i) begin
                        state = next_state;    
                    end
                end
                
                /*
                REQUESTING: Com o request já em nível alto, teremos que aguardar o handshake acontecer,
                ou seja, aguardar o obi_gnt_i ser igual a 1 no mesmo momento em que o obi_req_o é igual
                a 1, nesse momento devemos passar todos os dados para a memória, e passar para o proximo
                estado.
                */
                REQUESTING: begin
                    if (obi_gnt_i && core_valid_i)
                        state = next_state;
                    if(~core_valid_i)
                        state = IDLE;
                end

                /*
                WAITING: Enviados Todos os dados para a memória devemos aguardar sua resposta, desse modo, 
                nesse estado, vamos apenas aguardar o sinal obi_rvalid_i, para que possamos coletar os dados
                guardálos em registradores e passar para o requisitante, no caso, o core. Após isso 
                passaremos para o próximo estado.
                */
            
                WAITING: begin
                    if (obi_rvalid_i)
                        state = next_state;
                end

                /*
                DUMPING: Estado auxiliar para permanecer com os valores por mais de um ciclo de clock até que o
                hanshake entre o core e a memória seja satisfeito, assegurando que o dado requisitado chegue ao core.
                */

                DUMPING: begin
                        state = next_state;
                end
            endcase
        end
    end

    always_comb begin
        case(state)
            IDLE:       begin
                next_state      = REQUESTING;
                if (core_valid_i) begin

                    obi_addr_o      = {addr_aux_i[31:2],2'b0};
                    obi_we_o        = we_aux_i;
                    obi_be_o        = be_aux_i
                    obi_wdata_o     = wdata_aux_i;  
                    addr_aux_i      = core_addr_i;
                    we_aux_i        = core_we_i;
                    be_aux_i        = core_be_i;
                    wdata_aux_i     = core_wdata_i;
                    obi_req_o       = 1;
                    
                end
                else begin
                    obi_req_o = 0;
                end
                
            end

            REQUESTING: begin

                next_state      = WAITING;
                obi_req_o       = 1;
                
                obi_addr_o      = {addr_aux_i[31:2],2'b0};
                obi_we_o        = we_aux_i;
                obi_be_o        = be_aux_i
                obi_wdata_o     = wdata_aux_i;
               
            end
            WAITING:    begin
                next_state      = DUMPING;
                obi_req_o       = 0;
                if (obi_rvalid_i) begin
                    resp_rdata_o    = obi_rdata_i;
                    rdata_aux_i     = obi_rdata_i;
                end
            end
            DUMPING:    begin  // resp_valid_o
                next_state      = IDLE;
                obi_req_o       = 0;
                resp_rdata_o    = rdata_aux_i;
            end
            default: 
                next_state      = IDLE;
        endcase
    end

endmodule

// é necessário revisão/discussão a respeito do endereçamento da memória
                /* ------- VAI PARA O CORE -------

                unique case(mem_data_type_i)
                    WORD:  obi_be_o = 4'b1111;
                    HALF_WORD: begin
                        unique case(core_addr_i[4:3])
                            2'd3: obi_be_o = 4'b1000; // ESTÁ CERTO ISSO? DISCUTIR COM VH E COM PEDRO
                            2'd2: obi_be_o = 4'b1100;
                            2'd1: obi_be_o = 4'b0110;
                            2'd0: obi_be_o = 4'b0011;
                        endcase
                    end
                    BYTE: begin
                        unique case (core_addr_i[4:3])
                        2'd3:       obi_be_o = 4'b1000;
                        2'd2:       obi_be_o = 4'b0100;
                        2'd1:       obi_be_o = 4'b0010;
                        2'd0:       obi_be_o = 4'b0001;
                        default:    obi_be_o = 0;
                        endcase
                    end
                    default:        obi_be_o = 0;
                endcase
                */

            