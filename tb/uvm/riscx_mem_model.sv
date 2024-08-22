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
    
    // loads .bin into the memory
    // function void load_memory (string bin_file, section_info_t sections[$]);
    //     int fd;
    //     logic [31:0] addr, word;
    //     // int i, n;
    //     int n;
    //     logic [31:0] align_mask;

    //     // Open .bin file
    //     fd = $fopen(bin_file, "r");
    //     if (fd == 0) begin
    //         $fatal(1, "Failed to open %s.", bin_file);
    //     end

    //     // $display("Number of sections = %0d.", sections.size());
        
    //     // Load data into memory according to the sections information
    //     // We assume that sections[0] is the first section (lowest start address)
    //     addr = sections[0].start_addr;
    //     foreach (sections[i]) begin
    //         // $display("Addr at start of %s. Addr = 0x%h.", sections[i].name, addr);
            
    //         align_mask = (32'b1 << sections[i].alignment) - 1;
    //         // $display("align_mask = %h.", align_mask);
            
    //         if (addr & align_mask != '0) begin
    //             $display("addr && align_mask = 0x%h.", addr && align_mask);
    //             $display("Found misalignment for section %s. Addr = 0x%h, alignment = %0d.", sections[i].name, sections[i].start_addr, sections[i].alignment);
    //         end
            
    //         while (addr <= sections[i].end_addr) begin
    //             n = $fread(word, fd);
    //             if (n != 4 && n != 2) begin
    //                 $display("n = %0d.", n);
    //                 $fatal(1, "Error reading .bin at address 0x%h.", addr);
    //             end
                
    //             if (sections[i].name.substr(0,7) == ".region_") begin
    //                 // Account for endianess
    //                 word = {word[7:0], word[15:8], word[23:16], word[31:24]};
    //                 mem[addr] = word;
    //             end 
    //             if (sections[i].name == ".text") begin
    //                 // Account for endianess
    //                 word = {word[7:0], word[15:8], word[23:16], word[31:24]};
    //                 mem[addr] = word;
    //             end 
                
    //             addr += 4;
    //         end
    //     end

    //     // Close the file
    //     $fclose(fd);
    // endfunction
    
    function void load_memory (string bin_file);
        string error_desc;
        int file = $fopen(bin_file, "r");
        int errno = $ferror(file, error_desc);

        if (errno != 0) begin
            `uvm_fatal("MEM_MODEL", $sformatf("Cannot open %s for reading (error description: %s)", bin_file, error_desc))
        end
        //else begin
            //$fclose(file);
            //`uvm_info("MEM_MODEL", $sformatf("Loading memory contents from %s", bin_file), UVM_LOW)
            //$readmemh(bin_file, mem);
        //end
        
        
    endfunction

    // prints the entire memory
    function void print_mem ();
        foreach(mem[i])
            // $display("[MEM_MODEL]: mem[%h] = 0x%h.", i, mem[i]);
            `uvm_info("MEM_MODEL", $sformatf("mem[%h] = 0x%h.", i, mem[i]), UVM_LOW)
    endfunction

    // prints a single section
    // function void print_section (section_info_t section, int stop = 100);
    //     int k;
    //     $display("%t: Printing section %s of size 0x%h.", $time, section.name, section.size);
    //     k = 0;
    //     for (int j = section.start_addr; j <= section.end_addr; j += 4) begin
    //         if (k == stop) break;
    //         $display("%s[0x%h] = 0x%h", section.name, j, mem[j]);
    //         k++;
    //     end
    // endfunction
    
    // delete memory contents
    function void delete_mem ();
        mem.delete();
    endfunction
    
endclass : riscx_mem_model