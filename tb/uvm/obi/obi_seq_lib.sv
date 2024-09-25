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
// Design Name:    OBI sequence library                                       //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    OBI sequence library.                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class obi_base_sequence #(int XLEN=32, int ALEN=32) extends uvm_sequence#(obi_tr#(XLEN, ALEN));

    obi_cfg   cfg;
    obi_cntxt cntxt;
    riscx_mem_model mem;

    `uvm_object_utils(obi_base_sequence)
    `uvm_declare_p_sequencer(obi_seqr#(XLEN, ALEN))

    function new(string name="obi_base_sequence");
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
        `uvm_info("OBI SEQUENCE", "phase.raise_objection", UVM_HIGH)
    endtask: pre_body

    task post_body();
        uvm_phase phase = get_starting_phase();
        phase.drop_objection(this, get_type_name());
        `uvm_info("OBI SEQUENCE", "phase.drop_objection", UVM_HIGH)
    endtask: post_body

endclass: obi_base_sequence

//==============================================================//

class obi_random_seq #(int XLEN=32, int ALEN=32) extends obi_base_sequence#(XLEN, ALEN);

    `uvm_object_utils(obi_random_seq)

    function new(string name="obi_random_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        obi_tr mon_tr;
        int id;
        logic [31:0] addr, rdata;
        
        id = 0;
        repeat(10) begin
            p_sequencer.mon_tr_fifo.get(mon_tr);
            // `uvm_info("OBI RND SEQ", $sformatf("Got transaction from monitor:\n%s", mon_tr.sprint()), UVM_HIGH)
            `uvm_info("OBI RND SEQ", "Got transaction from monitor.", UVM_HIGH)
            
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
                foreach (mon_tr.be[i]) begin
                    // if (mem.exists(addr)) begin
                    // end
                    if (mon_tr.be[i])
                        rdata[i*8+:8] = mem.read (addr+i);
                    else
                        rdata[i*8+:8] = 8'b0;
                end
                req.rdata = rdata;
            end
            
            // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            
            req.id = id;
            id++;
            `uvm_send(req)
            
        end
    endtask: body

endclass: obi_random_seq

//==============================================================//

class obi_load_mem_seq #(int XLEN=32, int ALEN=32) extends obi_base_sequence#(XLEN, ALEN);

    `uvm_object_utils(obi_load_mem_seq)

    function new(string name="obi_load_mem_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        `uvm_info("OBI LOAD SEQ", "Running load memory sequence.", UVM_MEDIUM)
        mem.load_memory (cfg.mem_bin_file, cfg.mem_start_addr);
        // mem.print_section(cfg.mem_start_addr, cfg.mem_start_addr+32'hff);
    endtask: body

endclass: obi_load_mem_seq

//==============================================================//

class obi_memory_seq #(int XLEN=32, int ALEN=32) extends obi_base_sequence#(XLEN, ALEN);

    `uvm_object_utils(obi_memory_seq)

    function new(string name="obi_memory_seq");
        super.new(name);
    endfunction: new
    
    virtual task body();
        obi_tr mon_tr;
        int id;
        logic [31:0] addr, rdata;
        
        `uvm_info("OBI MEM SEQ", $sformatf("Started memory sequence."), UVM_LOW)
        
        id = 0;
        forever begin
            p_sequencer.mon_tr_fifo.get(mon_tr);
            // `uvm_info("OBI RND SEQ", $sformatf("Got transaction from monitor:\n%s", mon_tr.sprint()), UVM_HIGH)
            // `uvm_info("OBI RND SEQ", "Got transaction from monitor.", UVM_HIGH)
            
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
                foreach (mon_tr.be[i]) begin
                    // if (mem.exists(addr)) begin
                    // end
                    if (mon_tr.be[i])
                        rdata[i*8+:8] = mem.read (addr+i);
                    else
                        rdata[i*8+:8] = 8'b0;
                end
                req.rdata = rdata;
            end
            
            // void'(req.randomize() with {field_1==value_1; field_2==value_2;});
            
            req.id = id;
            id++;
            `uvm_send(req)
            
        end
        
        `uvm_info("OBI MEM SEQ", $sformatf("Finished memory sequence."), UVM_LOW)
    endtask: body

endclass: obi_memory_seq

//==============================================================//
