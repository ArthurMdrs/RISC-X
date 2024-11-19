<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>42</insertion-point-position>
  <wave>
    <expr>clock</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>pc_fwd</label>
    <wave collapsed="true">
      <expr>checker_inst.insn_order</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>checker_inst.expect_pc</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>checker_inst.expect_pc_valid</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>rvfi_valid</label>
    <wave>
      <expr>wrapper.core_inst.valid_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.valid_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.valid_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.valid_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.rvfi_valid_wb</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="true">
    <expr/>
    <label>Intr</label>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.next_pc_mux</expr>
      <label/>
      <radix>wrapper.rvfi_inst.next_pc_mux</radix>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.intr_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.intr_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.intr_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.intr_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.intr_wb</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>PC</label>
    <wave collapsed="true">
      <expr>wrapper.core_inst.pc_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.core_inst.if_stage_inst.pc_constroller_inst.next_pc_mux</expr>
      <label/>
      <radix>wrapper.rvfi_inst.next_pc_mux</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.core_inst.if_stage_inst.pc_if_n</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_n_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_n_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.pc_n_wb</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave>
    <expr>wrapper.rvfi_inst.rvfi_valid</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>Instr</label>
    <wave collapsed="true">
      <expr>wrapper.core_inst.instr_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.instr_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.instr_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.instr_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.instr_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rvfi_order</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>Trap</label>
    <wave>
      <expr>wrapper.core_inst.trap_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.trap_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.rvfi_trap_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.trap_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.rvfi_inst.trap_wb</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>Control</label>
    <wave>
      <expr>wrapper.core_inst.flush_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.flush_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.flush_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.stall_if</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.stall_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>wrapper.core_inst.stall_ex</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="true">
    <expr/>
    <label>rs1</label>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_addr_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_addr_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_addr_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_addr_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_or_fwd_id</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_rdata_ex</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_rdata_mem</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs1_rdata_wb</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
  </group>
  <group collapsed="true">
    <expr/>
    <label>rs2</label>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_addr_id</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_addr_ex</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_addr_mem</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_addr_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_or_fwd_id</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_rdata_ex</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_rdata_mem</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rs2_rdata_wb</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>rd</label>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rd_addr_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rvfi_rd_addr</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.reg_wdata_wb</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.rvfi_rd_wdata</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>Mem</label>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.mem_addr_wb</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.mem_rmask_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.mem_rdata_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.mem_wmask_wb</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>wrapper.rvfi_inst.mem_wdata_wb</expr>
      <label/>
      <radix>wrapper.rvfi_inst.rs1_or_fwd_id</radix>
    </wave>
  </group>
  <highlightlist>
    <!--Users can remove the highlightlist block if they want to load the signal save file into older version of Jasper-->
    <highlight>
      <expr>wrapper.core_inst.flush_ex</expr>
      <color>builtin_green</color>
    </highlight>
    <highlight>
      <expr>wrapper.core_inst.flush_id</expr>
      <color>builtin_green</color>
    </highlight>
    <highlight>
      <expr>wrapper.core_inst.flush_mem</expr>
      <color>builtin_green</color>
    </highlight>
    <highlight>
      <expr>wrapper.core_inst.if_stage_inst.pc_if_n</expr>
      <color>builtin_blue</color>
    </highlight>
    <highlight>
      <expr>checker_inst.insn_spec.spec_pc_wdata</expr>
      <color>#beffc0</color>
    </highlight>
    <highlight>
      <expr>checker_inst.insn_spec.spec_rd_addr</expr>
      <color>#beffc0</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.instr_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.intr_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.pc_id</expr>
      <color>#55ffff</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.pc_if</expr>
      <color>#55ffff</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.pc_n_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.pc_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rs1_addr_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rs1_rdata_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rs2_addr_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rs2_rdata_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rvfi_rd_addr</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rvfi_rd_wdata</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.rvfi_valid_wb</expr>
      <color>#ff8787</color>
    </highlight>
    <highlight>
      <expr>wrapper.rvfi_inst.trap_wb</expr>
      <color>#ff8787</color>
    </highlight>
  </highlightlist>
</wavelist>
