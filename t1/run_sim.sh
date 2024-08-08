#!/bin/bash

# Definindo o comando a ser executado
CMD="xrun -access +r -uvm +uvm_set_config_int=*,recording_detail,1 -coverage all -covoverwrite -DSYSTEM_CLOCK_UNITS_PER_SECOND=100 -timescale 1ns/1ns ../bvm/system_clock.c +incdir+../bvm ../bvm/bvm_pkg.sv dut.sv interface.sv test_pkg.sv top.sv +UVM_VERBOSITY=LOW"

# Executando o comando
echo "Executando o comando: $CMD"
$CMD

# Verificando o status da execução
if [ $? -eq 0 ]; then
    echo "Comando executado com sucesso!"
else
    echo "Houve um erro na execução do comando."
fi

