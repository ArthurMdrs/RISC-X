class mem_model;
    
    logic [31:0] data_mem [logic [31:0]];
    
    // Constructor
    function new();
    endfunction

    // get a data value from the memory
    function automatic void store_to_mem (logic [31:0] addr, logic [3:0] ben, logic [31:0] wdata);
        logic [31:0] addr_int, wdata_int;
        addr_int = {addr[31:2], 2'b0}; // We can only access 4-byte aligned addresses
        wdata_int = '0;
        if (data_mem.exists(addr_int)) wdata_int = data_mem[addr_int];
        case (addr[1:0])
            2'b00: begin
                if(ben[0]) wdata_int[ 7: 0] = wdata[ 7: 0];
                if(ben[1]) wdata_int[15: 8] = wdata[15: 8];
                if(ben[2]) wdata_int[23:16] = wdata[23:16];
                if(ben[3]) wdata_int[31:24] = wdata[31:24];
                data_mem[addr_int] = wdata_int;
            end
            2'b01: begin
                if(ben[0]) wdata_int[15: 8] = wdata[ 7: 0];
                if(ben[1]) wdata_int[23:16] = wdata[15: 8];
                if(ben[2]) wdata_int[31:24] = wdata[23:16];
                data_mem[addr_int] = wdata_int;
                if(ben[3]) begin
                    addr_int += 32'd4;
                    store_to_mem (addr_int, 4'b0001, {24'b0, wdata[31:24]});
                end
            end
            2'b10: begin
                if(ben[0]) wdata_int[23:16] = wdata[ 7: 0];
                if(ben[1]) wdata_int[31:24] = wdata[15: 8];
                data_mem[addr_int] = wdata_int;
                if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    store_to_mem (addr_int, 4'b0011, {16'b0, wdata[31:16]});
                end
            end
            2'b11: begin
                if(ben[0]) wdata_int[31:24] = wdata[ 7: 0];
                data_mem[addr_int] = wdata_int;
                if(ben[3:1] == 3'b001) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    store_to_mem (addr_int, 4'b0001, {24'b0, wdata[15:8]});
                end
                else if(ben[3:1] == 3'b111) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    store_to_mem (addr_int, 4'b0111, {8'b0, wdata[31:8]});
                end
            end
        endcase
    endfunction

    // put a data value in the memory
    function automatic void load_from_mem (logic [31:0] addr, logic [3:0] ben, output logic [31:0] rdata);
        logic [31:0] addr_int, rdata_int, rdata_aux;
        addr_int = {addr[31:2], 2'b0}; // We can only access 4-byte aligned addresses
        rdata_int = '0;
        if (data_mem.exists(addr_int)) rdata_int = data_mem[addr_int];
        case (addr[1:0])
            2'b00: begin
                // if(ben[0]) rdata_int[ 7: 0] = wdata[ 7: 0];
                // if(ben[1]) rdata_int[15: 8] = wdata[15: 8];
                // if(ben[2]) rdata_int[23:16] = wdata[23:16];
                // if(ben[3]) rdata_int[31:24] = wdata[31:24];
                rdata = rdata_int;
            end
            2'b01: begin
                rdata_int = rdata_int >> 8;
                rdata = rdata_int;
                if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    load_from_mem (addr_int, 4'b0001, rdata_aux);
                    rdata[31:24] = rdata_aux[7:0];
                end
            end
            2'b10: begin
                rdata_int = rdata_int >> 16;
                rdata = rdata_int;
                if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    load_from_mem (addr_int, 4'b0011, rdata_aux);
                    rdata[31:16] = rdata_aux[15:0];
                end
            end
            2'b11: begin
                rdata_int = rdata_int >> 24;
                rdata = rdata_int;
                if(ben[3:1] == 3'b001) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    load_from_mem (addr_int, 4'b0001, rdata_aux);
                    rdata[15:8] = rdata_aux[7:0];
                end
                else if(ben[3:1] == 3'b111) begin // We assume ben is one of: 0001, 0011, 1111
                    addr_int += 32'd4;
                    load_from_mem (addr_int, 4'b0111, rdata_aux);
                    rdata[31:8] = rdata_aux[23:0];
                end
            end
        endcase
    endfunction
    
    // loads .bin into the memory
    function void load_memory (string bin_file, section_info_t sections[$]);
        int fd;
        logic [31:0] addr, word;
        // int i, n;
        int n;
        logic [31:0] align_mask;

        // Open .bin file
        fd = $fopen(bin_file, "r");
        if (fd == 0) begin
            $fatal(1, "Failed to open %s.", bin_file);
        end

        // $display("Number of sections = %0d.", sections.size());
        
        // Load data into memory according to the sections information
        // We assume that sections[0] is the first section (lowest start address)
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
                    $fatal(1, "Error reading .bin at address 0x%h.", addr);
                end
                
                if (sections[i].name.substr(0,7) == ".region_") begin
                    // Account for endianess
                    word = {word[7:0], word[15:8], word[23:16], word[31:24]};
                    data_mem[addr] = word;
                end 
                if (sections[i].name == ".text") begin
                    // Account for endianess
                    word = {word[7:0], word[15:8], word[23:16], word[31:24]};
                    data_mem[addr] = word;
                end 
                
                addr += 4;
            end
        end

        // Close the file
        $fclose(fd);
    endfunction

    // prints the entire memory
    function void print_data_mem ();
        foreach(data_mem[i])
            $display("%t: data_mem[%h] = 0x%h.", $time, i, data_mem[i]);
    endfunction

    // prints a single section
    function void print_section (section_info_t section, int stop = 100);
        int k;
        $display("%t: Printing section %s of size 0x%h.", $time, section.name, section.size);
        k = 0;
        for (int j = section.start_addr; j <= section.end_addr; j += 4) begin
            if (k == stop) break;
            $display("%s[0x%h] = 0x%h", section.name, j, data_mem[j]);
            k++;
        end
    endfunction

endclass