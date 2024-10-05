// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    RISC-X UVM virtual sequencer                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Controls all sequencers contained in RISC-X environment.   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class riscx_vseqr #(
    parameter int ILEN   = 32  // Instruction length in bits
) extends uvm_sequencer;

    // obi_cfg   cfg;
    // obi_cntxt cntxt;

    `uvm_component_utils(riscx_vseqr)
    // `uvm_component_utils_begin(riscx_vseqr)
    //     `uvm_field_object(cfg  , UVM_DEFAULT)
    //     `uvm_field_object(cntxt, UVM_DEFAULT)
    // `uvm_component_utils_end
    
    clknrst_sqr sequencer_clknrst;
    obi_seqr    instr_obi_seqr;
    obi_seqr    data_obi_seqr;
    
    typedef riscx_vseqr this_type;
    uvm_analysis_imp #(bit [ILEN-1:0], this_type) detected_insn_imp;
    
    bit rvvi_instr_detected = 0;
    bit should_drop_objection = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        detected_insn_imp  = new("detected_insn_imp" , this);
    endfunction: new

    // function void build_phase (uvm_phase phase);
    //     super.build_phase(phase);
    //     void'(uvm_config_db#(obi_cfg)::get(this, "", "cfg", cfg));
    //     if (cfg == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Config handle is null.")
    //     end      
    //     void'(uvm_config_db#(obi_cntxt)::get(this, "", "cntxt", cntxt));
    //     if (cntxt == null) begin
    //         `uvm_fatal("RISC-X V SEQUENCER", "Context handle is null.")
    //     end      
    // endfunction: build_phase
    
    virtual function void write (bit [ILEN-1:0] t);
        rvvi_instr_detected = 1;
        should_drop_objection = 1;
        `uvm_info("RISC-X VSEQUENCER", $sformatf("Detected instruction 0x%h.", t), UVM_MEDIUM)
    endfunction : write

endclass: riscx_vseqr