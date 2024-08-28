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
    input   logic               core_valid_i,
    output  logic               core_ready_o,
    input  logic [WIDTH-1:0]    core_addr_i,
    input  logic                core_we_i,
    //input  data_type_t          mem_data_type_i, --> core_be
    input logic [WIDTH-1:0]     core_wdata_i,

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
    //output logic [ 5:0]         obi_atop_o,
    input  logic [WIDTH-1:0]    obi_rdata_i,
    input  logic                obi_rvalid_i
    //input  logic                obi_err_i

);

    OBI_state_t                 state, next_state;     


    // Transaction response interface
    output logic                resp_valid_o,  // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
    output logic [WIDTH-1:0]    resp_rdata_o,
    output logic                resp_err_o,
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
                IDLE: begin
                    if (core_valid_i) begin                          // se não tiver nenhuma operação na fila e o core solicitar uma,
                        state = next_state;    
                    end
                end
                REQUESTING: begin
                    if (obi_gnt_i && obi_req_o)
                        state = next_state;
                end
                WAITING: begin
                    if (obi_rvalid_i)
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
                next_state      = REQUESTING;
                obi_req_o       = 0;
                obi_rvalid_i    = 0;
            end

            REQUESTING: begin
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

                next_state      = WAITING;
                obi_req_o       = 1;
                obi_rvalid_i    = 0;
                obi_addr_o      = {core_addr_i[31:2],2'b0};
                obi_we_o        = core_we_i;
                obi_wdata_o     = core_wdata_i;
               
            end
            WAITING:    begin
                next_state      = DUMPING;
                obi_req_o       = 0;
                obi_rvalid_i    = 0;
            end
            DUMPING:    begin
                next_state      = IDLE;
                obi_req_o       = 0;
                obi_rvalid_i    = 1;

                if (we_nxt) // podemos colocar ou não essa condição
                    data_out    = rdata;
            end
            default: 
                next_state      = IDLE;
        endcase
    end

endmodule