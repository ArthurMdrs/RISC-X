module memory_loader;

typedef struct {
    string       name;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
    logic [31:0] size;
    int          alignment;
} section_info_t;

section_info_t sections[$]; // Dynamic array of section information
// int unsigned memory[int unsigned]; // Associative array for memory
logic [31:0] memory [logic [31:0]]; // Associative array for memory

// function to read sections file and populate sections array
function void read_sections (string file_str);
    string line;
    string name;
    logic [31:0] start_addr, end_addr, size;
    int alignment;
    int fd, code;
    section_info_t section;

    // Open the file
    fd = $fopen(file_str, "r");
    if (fd == 0) begin
        $fatal(1, "Failed to open sections.txt");
    end

    // Skip the first line (header)
    code = $fgets(line, fd);

    // Read the rest of the lines
    while (!$feof(fd)) begin
        // Read section name
        code = $fscanf(fd, "%s\n", name);
        if(code == -1)
            break;
        
        // Read line with infos
        code = $fgets(line, fd);
        code = $sscanf(line, "%x,%x,%x,%d\n", start_addr, end_addr, size, alignment);

        // Add the section information to the array
        if (code == 4) begin
            section.name = name;
            section.start_addr = start_addr;
            section.end_addr = end_addr;
            section.size = size;
            section.alignment = alignment;
            sections.push_back(section);
        end else begin
            $fatal(1, "Wrong number of data.");
        end
    end

    // Close the file
    $fclose(fd);
endfunction

// function to load program.bin into the memory associative array
function void load_memory;
    int fd;
    logic [31:0] addr, word;
    int i, n;
    logic [31:0] align_mask;

    // Open program.bin
    fd = $fopen("/home/pedro.medeiros/Tools/riscv-formal-VeeR/cores/risc-x/RISC-X/tb/riscv-dv/mytest/asm_test/riscv_rand_instr_test_0.bin", "rb");
    if (fd == 0) begin
        $fatal(1, "Failed to open .bin file.");
    end

    $display("Number of sections = %0d.", sections.size());
    
    // Load data into memory according to the sections information
    addr = sections[0].start_addr;
    foreach (sections[i]) begin
        // $display("Addr at start of %s. Addr = 0x%h.", sections[i].name, addr);
        
        align_mask = (32'b1 << sections[i].alignment) - 1;
        // $display("align_mask = %h.", align_mask);
        
        if (addr & align_mask != '0) begin
            $display("addr && align_mask = 0x%h.", addr && align_mask);
            $display("Found misalignment for section %s. Addr = 0x%h, alignment = %0d.", sections[i].name, sections[i].start_addr, sections[i].alignment);
        end
        
        while (addr <= sections[i].end_addr) begin
            n = $fread(word, fd);
            if (n != 4) begin
                $fatal(1, "Error reading program.bin at address %h", addr);
            end
            // Account for endianess
            word = {word[7:0], word[15:8], word[23:16], word[31:24]};
            memory[addr] = word;
            addr += 4;
        end
        
        
        // THe code below will not work!!
        // for (addr = sections[i].start_addr; addr <= sections[i].end_addr; addr += 4) begin
        //     n = $fread(word, fd);
        //     if (n != 4) begin
        //         $fatal("Error reading program.bin at address %h", addr);
        //     end
        //     // Account for endianess
        //     word = {word[7:0], word[15:8], word[23:16], word[31:24]};
        //     memory[addr] = word;
        // end
        
        // $display("Addr at end of %s. Addr = 0x%h.", sections[i].name, addr);
    end

    // Close the file
    $fclose(fd);
endfunction

initial begin
    string sections_file;
    
    // Read section information
    sections_file = "/home/pedro.medeiros/Tools/riscv-formal-VeeR/cores/risc-x/RISC-X/tb/riscv-dv/mytest/asm_test/riscv_rand_instr_test_0.section";
    read_sections(sections_file);

    // Load memory with the binary data
    // load_memory();
    
    // foreach (sections[i])
    //     $display("Section %s: 0x%h, 0x%h, 0x%h, 2**%0d", sections[i].name, sections[i].start_addr, sections[i].end_addr, sections[i].size, sections[i].alignment);
    
    // foreach (memory[i])
    //     $display("Memory[0x%h] = 0x%h", i, memory[i]);
    
    // $display("Memory[0x80012048] = %h", memory[32'h80012048]);
    
    $display("Part select of a string: sections[0].name.substr(0,3) = %s", sections[0].name.substr(0,3));
    foreach (sections[i])
        $display("Part select of a string: sections[i].name.substr(0,7) = %s", sections[i].name.substr(0,7));
end

endmodule
