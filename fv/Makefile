VCD = ./violation.vcd
BATCH = -batch
TOOL = jg

# .SILENT:

run: run_checks

run_checks:
	@$(eval TIME_START = $(shell date))
	@if [ ! -d checks ]; then $(MAKE) gen_jg BATCH=$(BATCH); fi
	@make -C checks
	@echo Proccess start: $(TIME_START)
	@echo Proccess end  : $$(date)

gen_sby:
	@if [ -d checks ]; then $(MAKE) clean; fi
	@python3 ../../checks/genchecks.py
	@python3 ../../checks/insert_incdirs.py

gen_jg:
	@if [ -d checks ]; then $(MAKE) clean; fi
	@python3 ../../checks/genchecks_jg.py

gtkw:
	gtkwave $(VCD) checks.gtkw

disasm:
	python3 disasm.py $(VCD)

clean:
	@echo "Removing checks folder."
	@rm -rf checks *.sig~ jgproject 2> /dev/null || true

summary:
	@python3 gen_summary.py $(TOOL)
	@if [ -e summary.txt ]; then echo Created file \"summary.txt\".; fi

core:
	@echo "Updating submodules (the only submodule is the core)."
	@git submodule update --init --recursive

isa:
	@echo Generating instruction files in /path/to/riscv-formal/insns.
	@cd ../../insns && rm -f *.v *.txt
	@cd ../../insns && python3 generate.py