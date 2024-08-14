
# RISC-X

---

## OBI IMPLEMENTATION

    Esta branch é focada em adicionar a interface tipo OBI ao processador RISC-X.


## What is OBI

    O Open Bus Interface (OBI) consiste em uma interface utilizada para comunicação entre o processador
    com o restante do Core, que contem os sinais:

### Sinais Globais:
    
    clk - Sinal de clock endereçado a todo o chip
    reset_n - Sinal de Reset sensivel a borda negativa.

### Modulo Manager/Mestre:

    req - Indica para o subordinado que vai existir uma transferencia e os dados já são válidos;
    addr - Indica o Endereço que está sendo acessado;
    we - Identifica se ocorrerá uma leitura ou escrita (1 = WRITE;0 = READ);
    be - Indica quais Bytes podem ser escritos/lidos; Ex: {be = 0001}, só os 8 últimos bits serão lidos ou escritos.
    wdata - Dado que enviado ao subordinado para ser armazenado no endereço indicado, caso seja uma operação de escrita (we = 1);
    rready - Indica ao Subordinado que está disponível/pronto para receber uma resposta.
    
### Modulo Subordinado/Escravo:

    gnt - Indica que o Subordinado está pronto para receber nova requisição;
    rvalid - O dado Requisitado está pronto;
    rdata - Dados requisitados pelo Manager.
    
## Aspectos Relevantes

    O OBI é aplicável a sistemas Little-endian.

## Desenvolvedores

    Tulio Tavares   (tulio.tavares@ee.ufcg.edu.br)
    Victor Hugo     (victor.klein@ee.ufcg.edu.br)



by Túlio
