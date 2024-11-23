# Especificação Multiplier Handshake

## Index
- [Descrição](#Descrição)
- [Recursos](#Recursos)
- [Simulação](#Simulação)
- [Versão](#Versão)

## Descrição Funcional

- Multiplicador de 32x32bits
- Sincronização Handshake
- Suporte para as 4 operações RISC-V: MUL, MULH, MULHSU e MULHU

Operações de produto 32x32 RISC-V:
```
|---------------------------------------------------------------------------------------------------------------|
| Instrução |     Operandos                |  Retorno       |                Descrição                          |
|---------------------------------------------------------------------------------------------------------------|
|  MUL      |  Signed(a)   x Signed(b)     |  Res. completo |  Produto normal com sinal                         |
|  MULH     |  Signed(a)   x Signed(b)     |  Bits altos    |  Bits superiores do Produto com sinal             |
|  MULHSU   |  Signed(a)   x Unsigned(b)   |  Bits altos    |  Bits superiores do Produto com sinal e sem sinal |
|  MULHU    |  Unsigned(a) x Unsigned(b)   |  Bits altos    |  Bits superiores do Produto sem sinal             |
|---------------------------------------------------------------------------------------------------------------|
```

Pinos de Entrada/Saída:
```
|---------------------------------------------------------------------------------------------------------------|
|  Nome         |  Direção  |  Tamanho  |                        Descrição                                      |
|---------------------------------------------------------------------------------------------------------------|
|  clk          |  Entrada  |  1bit     |  Sinal de clock                                                       |
|  rst_n        |  Entrada  |  1bit     |  Sinal de reset ativo baixo                                           |
|  a            |  Entrada  |  32bits   |  1º Operando de 32 bits                                               |
|  b            |  Entrada  |  32bits   |  2º Operando de 32 bits                                               |
|  in_valid_i   |  Entrada  |  1bit     |  Habilita a multiplicação                                             |
|  out_ready_i  |  Entrada  |  1bit     |  Habilita escrita                                                     |
|  op_sel       |  Entrada  |  2bits    |  Tipo de operação RISC-V                                              |
|  in_ready_o   |  Saída    |  1bit     |  Sinal que indica que o multiplicador está pronto para iniciar        |
|  out_valid_o  |  Saída    |  1bit     |  Sinal que indica que o resultado é válido                            |
|  resultado    |  Saída    |  32bits   |  Resultado da multiplicação, 64 bits                                  |
|---------------------------------------------------------------------------------------------------------------|
```

Configuração de dados de entrada:
```
[31:0] a: 1º Operando de 32 bits
  Armazena no bit [i] os dados de entrada a[i]
[31:0] b: 2º Operando de 32 bits
  Armazena no bit [i] os dados de entrada b[i]
in_valid_i: Habilita a multiplicação
  Sinal de início para começar a multiplicação
    - 1: Inicia a multiplicação
    - 0: Não inicia a multiplicação
out_ready_i: Habilita escrita
  Sinal que indica que o receptor está pronto para receber novos dados
    - 1: Está pronto
    - 0: Não está pronto
op_sel: Tipo de operação RISC-V
  Seleciona a operação RISC-V
    - 00: MUL
    - 01: MULH
    - 10: MULHSU
    - 11: MULHU
```

## Recursos

```
Xcelium Simulator 2024

Simvision 2024
```

## Simulação

Para iniciar a simulação utilize o comando:
```
make sim
```

Para iniciar o simvision utilize:
```
make wave
```

Para mais instruções utilize:
```
make help
```

## Versão

Versão do RTL e Testbench totalmente operacionais.
