# Multiplier Handshake

## Index
- [Descrição](#Descrição)
- [Especificação](#Especificação)
- [Status](#Status)
- [Recursos](#Recursos)
- [Simulação](#Simulação)
- [Versão](#Versão)

## Descrição

Multiplicador de 32x32bits utilizando Valid e Ready e a lógica do [algoritmo de multiplicação de Booth](https://en.wikipedia.org/wiki/Booth%27s_multiplication_algorithm).

# Especificação

O módulo RTL do multiplicador possui os seguintes sinais:
```
|-------------------------------------------------------------------------------------------------------|
|  Nome      |  Direção  |  Tamanho  |                        Descrição                                 |
|-------------------------------------------------------------------------------------------------------|
|  clk       |  Entrada  |  1bit     |  Sinal de clock                                                  |
|  reset_n   |  Entrada  |  1bit     |  Sinal de reset ativo baixo                                      |
|  a         |  Entrada  |  32bits   |  1º Operando de 32 bits                                          |
|  b         |  Entrada  |  32bits   |  2º Operando de 32 bits                                          |
|  valid_in  |  Entrada  |  1bit     |  Sinal de início para começar a multiplicação                    |
|  ready     |  Entrada  |  1bit     |  Sinal que indica que o multiplicador está pronto para iniciar   |
|  nclocks   |  Entrada  |  32bits   |  Número de ciclos de clock para a multiplicação (Sempre 32bits)  |
|  c         |  Saída    |  32bits   |  Resultado da multiplicação, 64 bits                             |
|  valid_out |  Saída    |  1bit     |  Sinal que indica que o resultado é válido                       |
|-------------------------------------------------------------------------------------------------------|
```

## Status

O testbench valida os seguintes testes de multiplicação 32x32bits:
```
- Valor fixo
- Valores aleatórios
- Valores limite
- Valores mínimos
- Valor pequeno e grande
- Valores negativos.
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
