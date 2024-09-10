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
// Design Name:    RISC-X UVM memory model                                    //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines a byte-addressable memory model, with functions    //
//                 to load, write, initialize, etc.                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class riscx_mem_model #(int ALEN=32) extends uvm_object;
    
    logic [7:0] mem [logic [ALEN-1:0]];

   `uvm_object_param_utils(riscx_mem_model#(ALEN))
    
    // Constructor
    function new(string name = "riscx_mem_model");
        super.new(name);
    endfunction

    // write a data value to the memory
    virtual function void write (logic [ALEN-1:0] addr, logic [7:0] wdata);
        mem[addr] = wdata;
    endfunction

    // read a data value from the memory
    function logic [7:0] read (logic [ALEN-1:0] addr);
        if(mem.exists(addr)) begin
            return mem[addr];
        end
        else begin
            return 7'b0;
        end
    endfunction
    
    function void load_memory (string bin_file, logic [ALEN-1:0] start_addr);
        string error_desc;
        logic [7:0] my_byte;
        logic [ALEN-1:0] addr;
        int file, errno, n;
        
        file = $fopen(bin_file, "r");
        errno = $ferror(file, error_desc);

        if (errno != 0) begin
            `uvm_fatal("MEM_MODEL", $sformatf("Cannot open %s for reading (error description: %s)", bin_file, error_desc))
        end
        else begin
            `uvm_info("MEM_MODEL", $sformatf("Loading memory contents from %s", bin_file), UVM_HIGH)
            n = 0;
            addr = start_addr;
            do begin
                n = $fread(my_byte, file);
                mem[addr] = my_byte;
                addr++;
            end while(n != 0);
        end
        
        $fclose(file);
    endfunction

    // prints the entire memory
    function void print_mem ();
        `uvm_info("MEM_MODEL", "Printing entire memory.", UVM_HIGH)
        foreach(mem[i])
            // $display("[MEM_MODEL]: mem[%h] = 0x%h.", i, mem[i]);
            `uvm_info("MEM_MODEL", $sformatf("mem[%h] = 0x%h.", i, mem[i]), UVM_HIGH)
    endfunction

    // prints a memory section
    function void print_section (logic [ALEN-1:0] addr_start, logic [ALEN-1:0] addr_end);
        `uvm_info("MEM_MODEL", $sformatf("Printing memory in range [%h, %h].", addr_start, addr_end), UVM_HIGH)
        for (logic [ALEN-1:0] j = addr_start; j <= addr_end; j++) begin
            `uvm_info("MEM_MODEL", $sformatf("mem[%h] = 0x%h.", j, mem[j]), UVM_HIGH)
        end
    endfunction
    
    // delete memory contents
    function void delete_mem ();
        mem.delete();
    endfunction
    
    // returns 1 if addr exists
    function bit exists (logic [ALEN-1:0] addr);
        return mem.exists(addr);
    endfunction
    
endclass : riscx_mem_model