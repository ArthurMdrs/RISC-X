#IFS = ../src_uvm/udma_uart_if.sv
#PKG = ../src_uvm/udma_uart_pkg.sv
#RTL = ../rtl/*.sv  
#INC = /home/xmen/Desktop/microverif/udma_uart/validation/uart/testbench/udma_uart_includes.sv

# ========================== IS THIS COMMIT? ===========================

run: clean
	clear
	xrun ../testbench/udma_uart_tb.sv -gui -access +rw -input ./waves.tcl 

clean:
	@rm -rf INCA_libs waves.shm cov_work/ *.history *.log *.key mdv.log imc.log imc.key ncvlog_*.err *.trn *.dsn .simvision/ simvision* xcelium.d simv.daidir *.so *.o *.err

view_waves:


erros:
	grep "*E" xrun.log > erros.txt
	vim erros.txt	
