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
// Design Name:    RISC-X UVM virtual sequence library                        //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines virtual sequences.                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class riscx_base_vseq extends uvm_sequence;

    // obi_cfg   cfg;
    // obi_cntxt cntxt;

    `uvm_object_utils(riscx_base_vseq)
    `uvm_declare_p_sequencer(riscx_vseqr)

    function new(string name="riscx_base_vseq");
        super.new(name);
    endfunction: new

    // task pre_start();
    //     cfg   = p_sequencer.cfg;
    //     cntxt = p_sequencer.cntxt;
    // endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("RISC-X Sequence", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("RISC-X Sequence", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: riscx_base_vseq

//==============================================================//

class riscx_random_vseq extends riscx_base_vseq;

    `uvm_object_utils(riscx_random_vseq)
    
    obi_load_mem_seq obi_load_mem_seq_inst;
    obi_random_seq   obi_random_seq_inst;

    function new(string name="riscx_random_vseq");
        super.new(name);
    endfunction: new
    
    // If a sequence is called via a `uvm_do variant, then it is defined as a 
    // subsequence and it's pre/post_body() methods are not executed
    virtual task body();
        `uvm_do_on(obi_load_mem_seq_inst, p_sequencer.instr_obi_seqr);
        `uvm_do_on(obi_random_seq_inst  , p_sequencer.instr_obi_seqr);
    endtask: body

endclass: riscx_random_vseq