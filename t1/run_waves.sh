#!/bin/bash

# Definindo o comando a ser executado
CMD="simvision waves.shm"

# Executando o comando
echo "Executando o comando: $CMD"
$CMD

# Verificando o status da execução
if [ $? -eq 0 ]; then
    echo "Comando executado com sucesso!"
else
    echo "Houve um erro na execução do comando."
fi

