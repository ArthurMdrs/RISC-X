# Multiplier Handshake

## Index
- [Descrição](#Descrição)
- [Status atual](#Status_atual)
- [Recursos](#Recursos)
- [Simulação](#Simulação)
- [Versão estável](#Versão_estável)

## Descrição

Multiplicador de 32x32bits utilizando Valid e Ready e a lógica do [algoritmo de multiplicação de Booth](https://en.wikipedia.org/wiki/Booth%27s_multiplication_algorithm).

## Status atual

O testbench valida os seguintes testes:
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

## Versão estável

Versão Testbench totalmente operacional
