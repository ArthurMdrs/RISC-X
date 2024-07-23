clear -all

set rtl_home $env(RTL_HOME)
set rvfi_home $env(RVFI_HOME)

analyze -sv12 -f $rtl_home/file_list.f
analyze -sv12 ./rvfi_defines.sv
analyze -sv12 $rvfi_home/rvfi.sv
analyze -sv12 ./rvviTrace.sv ./rvvi_wrapper.sv

elaborate -top rvvi_wrapper -create_related_covers witness 

clock clk_i
reset !rst_n_i

prove -bg -all
