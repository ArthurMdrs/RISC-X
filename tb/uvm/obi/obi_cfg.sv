class obi_cfg #(int XLEN=32, int ALEN=32) extends uvm_object;

    logic some_flag;
    logic [ALEN-1:0] mem_start_addr;
   
    `uvm_object_param_utils_begin(obi_cfg)
        `uvm_field_int(some_flag, UVM_ALL_ON)
        `uvm_field_int(mem_start_addr, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "obi_cfg");
        super.new(name);
    endfunction: new
   
endclass : obi_cfg