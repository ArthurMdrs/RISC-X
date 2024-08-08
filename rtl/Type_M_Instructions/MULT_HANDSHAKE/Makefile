DIR  		= mkdir -p ./work/
FILES  	= ../mult.sv \
					../tb_multiplier.sv

.PHONY: sim clean

sim:
	$(DIR) 
	cd ./work/ &&\
	xrun \
	-timescale 1ns/1ns \
	-sv -v93 \
	$(FILES) \
	-access +r \

wave:
	cd ./work/ &&\
	simvision waves.shm &

clean:
	rm -rf xrun.* *.log .simvision ./work/

help:
	@echo "Xcelium and VManager need to be installed and environment needs to be set up to use this Makefile."
	@echo "possible arguments to make:"
	@echo "sim - run simulation"
	@echo "wave - show waveforms and transaction diagrams after simulation"
	@echo "       use & to keep the waveform viewer open and reload database after next simulation"
	@echo "clean - remove simulation output files"
