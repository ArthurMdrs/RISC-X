${RTL_HOME}/pkg/core_pkg.sv
${TB_HOME}/tb_pkg.sv

+incdir+${RTL_HOME}/cvfpu_errado/common_cells/include
${RTL_HOME}/cvfpu_errado/common_cells/src/cf_math_pkg.sv
${RTL_HOME}/cvfpu_errado/common_cells/src/rr_arb_tree.sv
${RTL_HOME}/cvfpu_errado/common_cells/src/lzc.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_pkg.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_cast_multi.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_classifier.sv
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/clk/rtl/gated_clk_cell.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_ctrl.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_ff1.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_pack_single.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_prepare.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_round_single.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_special.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_srt_single.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_top.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fpu/rtl/pa_fpu_dp.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fpu/rtl/pa_fpu_frbus.v
${RTL_HOME}/cvfpu_errado/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fpu/rtl/pa_fpu_src_type.v
${RTL_HOME}/cvfpu_errado/src/fpnew_divsqrt_th_32.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_divsqrt_th_64_multi.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_divsqrt_multi.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_fma.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_fma_multi.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_noncomp.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_opgroup_block.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_opgroup_fmt_slice.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_opgroup_multifmt_slice.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_rounding.sv
${RTL_HOME}/cvfpu_errado/src/fpnew_top.sv

${RTL_HOME}/alu.sv
${RTL_HOME}/controller.sv
${RTL_HOME}/decoder.sv
${RTL_HOME}/imm_extender.sv
${RTL_HOME}/pc_controller.sv
${RTL_HOME}/register_file.sv
${RTL_HOME}/csr.sv

${RTL_HOME}/if_stage.sv
${RTL_HOME}/id_stage.sv
${RTL_HOME}/ex_stage.sv
${RTL_HOME}/mem_stage.sv
${RTL_HOME}/wb_stage.sv

${RTL_HOME}/core.sv

+incdir+${RVFI_HOME}
${RVFI_HOME}/rvfi_defines.sv
${RVFI_HOME}/rvfi_macros.vh
${RVFI_HOME}/rvfi.sv

+incdir+${RVVI_HOME}
${RVVI_HOME}/rvviTrace.sv
${RVVI_HOME}/rvvi_tracer.sv
${RVVI_HOME}/rvvi_wrapper.sv

${TB_HOME}/mem.sv
${TB_HOME}/rvvi_tb.sv
