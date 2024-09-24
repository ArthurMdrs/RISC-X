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

    // bad_uvc_cfg   cfg;
    // bad_uvc_cntxt cntxt;

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
    
    clknrst_reset_and_start_clk_seq clknrst_reset_and_start_clk_seq_inst;
    
    bad_uvc_load_mem_seq bad_uvc_load_mem_seq_inst;
    bad_uvc_random_seq   instr_bad_uvc_random_seq_inst;
    
    bad_uvc_random_seq   data_bad_uvc_random_seq_inst;

    function new(string name="riscx_random_vseq");
        super.new(name);
    endfunction: new
    
    // If a sequence is called via a `uvm_do variant, then it is defined as a 
    // subsequence and it's pre/post_body() methods are not executed
    virtual task body();
    
        `uvm_do_on(clknrst_reset_and_start_clk_seq_inst, p_sequencer.sequencer_clknrst);
        
        fork
            // begin : clknrst
                
            // end : clknrst
            
            begin : instr_bad_uvc
                `uvm_do_on(bad_uvc_load_mem_seq_inst    , p_sequencer.instr_bad_uvc_seqr);
                `uvm_do_on(instr_bad_uvc_random_seq_inst, p_sequencer.instr_bad_uvc_seqr);
            end : instr_bad_uvc
            
            begin : data_bad_uvc
                `uvm_do_on(data_bad_uvc_random_seq_inst, p_sequencer.data_bad_uvc_seqr);
            end : data_bad_uvc
        join
        
    endtask: body

endclass: riscx_random_vseq

//==============================================================//

class riscx_dv_vseq extends riscx_base_vseq;

    `uvm_object_utils(riscx_dv_vseq)
    
    clknrst_reset_and_start_clk_seq clknrst_reset_and_start_clk_seq_inst;
    
    bad_uvc_load_mem_seq bad_uvc_load_mem_seq_inst;
    bad_uvc_memory_seq   instr_bad_uvc_memory_seq_inst;
    
    bad_uvc_memory_seq   data_bad_uvc_memory_seq_inst;

    function new(string name="riscx_dv_vseq");
        super.new(name);
    endfunction: new
    
    // If a sequence is called via a `uvm_do variant, then it is defined as a 
    // subsequence and it's pre/post_body() methods are not executed
    virtual task body();
    
        `uvm_do_on(clknrst_reset_and_start_clk_seq_inst, p_sequencer.sequencer_clknrst);
        
        fork
            // begin : clknrst
                
            // end : clknrst
            
            // This block goes forever
            begin : instr_bad_uvc
                `uvm_do_on(bad_uvc_load_mem_seq_inst    , p_sequencer.instr_bad_uvc_seqr);
                `uvm_do_on(instr_bad_uvc_memory_seq_inst, p_sequencer.instr_bad_uvc_seqr);
            end : instr_bad_uvc
            
            // This block goes forever
            begin : data_bad_uvc
                `uvm_do_on(data_bad_uvc_memory_seq_inst, p_sequencer.data_bad_uvc_seqr);
            end : data_bad_uvc
            
            // Because of join_any, the fork block finishes when we get should_drop_objection
            begin : drop_objection
                wait (p_sequencer.should_drop_objection === 1'b1);
                `uvm_info("RISC-X Sequence", "Got signal to drop objection.", UVM_HIGH)
            end : drop_objection
        join_any
        
    endtask: body

endclass: riscx_dv_vseq

//==============================================================//