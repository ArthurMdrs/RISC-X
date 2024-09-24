RISC_X_ROOT   := $(abspath $(shell pwd)/../..)
PATCHES_ROOT  := $(abspath $(shell pwd))
TOOLS_ROOT    := $(abspath $(RISC_X_ROOT)/tools)

PATCH_NAME := changes

create-patch:
	cd $(TOOLS_ROOT)/riscv-dv && git diff > $(PATCHES_ROOT)/riscv-dv/$(PATCH_NAME).patch

apply-patch:
	cd $(TOOLS_ROOT)/riscv-dv && patch -p1 < $(PATCHES_ROOT)/riscv-dv/$(PATCH_NAME).patch

revert-patch:
	cd $(TOOLS_ROOT)/riscv-dv && patch -R < $(PATCHES_ROOT)/riscv-dv/$(PATCH_NAME).patch
