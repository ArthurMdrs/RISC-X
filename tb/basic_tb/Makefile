# SVA = +define+SVA_ON=1

RTL_HOME = ../../rtl
RTL = $(RTL_HOME)/pkg/*.sv $(RTL_HOME)/*.sv
# FV = ../fv/*.sv
# TB = ./core_tb.sv
TB = ./*.sv
TOP = -top core_tb

SEED = -svseed 2
INPUT = -input restore.tcl

run: sim

sim:
	xrun -64bit -sv +define+SIM $(RTL) $(FV) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ps -access +rwc $(SEED)

gui:
	xrun -64bit -sv +define+SIM $(RTL) $(FV) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ps -access +rwc $(SEED) -gui $(INPUT)

clean:
	rm -rf xcelium.d xrun* .simvision .symbol* waves*
