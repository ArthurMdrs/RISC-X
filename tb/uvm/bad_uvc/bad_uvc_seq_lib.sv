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
// Design Name:    Bad UVC sequence library                                   //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bad UVC sequence library.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class bad_uvc_base_sequence extends uvm_sequence#(bad_uvc_tr);

    bad_uvc_cfg   cfg;
    bad_uvc_cntxt cntxt;
    riscx_mem_model mem;

    `uvm_object_utils(bad_uvc_base_sequence)
    `uvm_declare_p_sequencer(bad_uvc_seqr)

    function new(string name="bad_uvc_base_sequence");
        super.new(name);
    endfunction: new

    task pre_start();
        cfg   = p_sequencer.cfg;
        cntxt = p_sequencer.cntxt;
        mem   = cntxt.mem;
    endtask: pre_start

    task pre_body();
        uvm_phase phase = get_starting_phase();
        phase.raise_objection(this, get_type_name());
        `uvm_info("BAD_UVC SEQUENCE", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("BAD_UVC SEQUENCE", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: bad_uvc_base_sequence

//==============================================================//

class bad_uvc_random_seq extends bad_uvc_base_sequence;

    `uvm_object_utils(bad_uvc_random_seq)

    function new(string name="bad_uvc_random_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        bad_uvc_tr mon_tr;
        int id;
        logic [31:0] addr, rdata;
        
        `uvm_info("BAD_UVC RND SEQ", $sformatf("Started random sequence."), UVM_LOW)
        
        id = 0;
        repeat(10) begin
            p_sequencer.mon_tr_fifo.get(mon_tr);
            // `uvm_info("BAD_UVC RND SEQ", $sformatf("Got transaction from monitor:\n%s", mon_tr.sprint()), UVM_HIGH)
            // `uvm_info("BAD_UVC RND SEQ", "Got transaction from monitor.", UVM_HIGH)
            
            `uvm_create(req)
            void'(req.randomize());
            
            addr = mon_tr.addr;
            if (mon_tr.we) begin
                foreach (mon_tr.be[i]) begin
                    if (mon_tr.be[i])
                        mem.write (addr+i, mon_tr.wdata[i*8+:8]);
                end
            end
            else begin
                // `uvm_info("BAD_UVC RND SEQ", $sformatf("Reading from addr %h", addr), UVM_NONE)
                foreach (mon_tr.be[i]) begin
                    // if (mem.exists(addr)) begin
                    // end
                    if (mon_tr.be[i])
                        rdata[i*8+:8] = mem.read (addr+i);
                    else
                        rdata[i*8+:8] = 8'b0;
                end
                req.rdata = rdata;
                // `uvm_info("BAD_UVC RND SEQ", $sformatf("Read %h", req.rdata), UVM_NONE)
            end
            
            // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            
            req.id = id;
            id++;
            `uvm_send(req)
            
        end
        
        `uvm_info("BAD_UVC RND SEQ", $sformatf("Finished random sequence."), UVM_LOW)
    endtask: body

endclass: bad_uvc_random_seq

//==============================================================//

class bad_uvc_load_mem_seq extends bad_uvc_base_sequence;

    `uvm_object_utils(bad_uvc_load_mem_seq)

    function new(string name="bad_uvc_load_mem_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("BAD_UVC LOAD SEQ", "Running load memory sequence.", UVM_MEDIUM)
        mem.load_memory (cfg.mem_bin_file, cfg.mem_start_addr);
        // mem.print_section(cfg.mem_start_addr, cfg.mem_start_addr+32'hff);
    endtask: body

endclass: bad_uvc_load_mem_seq

//==============================================================//

class bad_uvc_memory_seq extends bad_uvc_base_sequence;

    `uvm_object_utils(bad_uvc_memory_seq)

    function new(string name="bad_uvc_memory_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        bad_uvc_tr mon_tr;
        int id;
        logic [31:0] addr, rdata;
        
        `uvm_info("BAD_UVC RND SEQ", $sformatf("Started memory sequence."), UVM_LOW)
        
        id = 0;
        forever begin
            p_sequencer.mon_tr_fifo.get(mon_tr);
            // `uvm_info("BAD_UVC RND SEQ", $sformatf("Got transaction from monitor:\n%s", mon_tr.sprint()), UVM_HIGH)
            // `uvm_info("BAD_UVC RND SEQ", "Got transaction from monitor.", UVM_HIGH)
            
            `uvm_create(req)
            void'(req.randomize());
            
            addr = mon_tr.addr;
            if (mon_tr.we) begin
                foreach (mon_tr.be[i]) begin
                    if (mon_tr.be[i])
                        mem.write (addr+i, mon_tr.wdata[i*8+:8]);
                end
            end
            else begin
                // `uvm_info("BAD_UVC RND SEQ", $sformatf("Reading from addr %h", addr), UVM_NONE)
                foreach (mon_tr.be[i]) begin
                    // if (mem.exists(addr)) begin
                    // end
                    if (mon_tr.be[i])
                        rdata[i*8+:8] = mem.read (addr+i);
                    else
                        rdata[i*8+:8] = 8'b0;
                end
                req.rdata = rdata;
                // `uvm_info("BAD_UVC RND SEQ", $sformatf("Read %h", req.rdata), UVM_NONE)
            end
            
            // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            
            req.id = id;
            id++;
            `uvm_send(req)
            
        end
        
        `uvm_info("BAD_UVC MEM SEQ", $sformatf("Finished memory sequence."), UVM_LOW)
    endtask: body

endclass: bad_uvc_memory_seq

//==============================================================//
