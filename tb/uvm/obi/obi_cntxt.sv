class obi_cntxt #(int XLEN=32, int ALEN=32) extends uvm_object;

    riscx_mem_model mem;

    obi_reset_state_enum rst_state = OBI_RST_STATE_PRE_RESET;
    
    // int unsigned no_oustnd_tr;
   
    `uvm_object_param_utils_begin(obi_cntxt#(XLEN, ALEN))
        `uvm_field_enum(obi_reset_state_enum, rst_state, UVM_ALL_ON)
        // `uvm_field_int(no_oustnd_tr, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "obi_cntxt");
        super.new(name);
        
        mem = riscx_mem_model#(ALEN)::type_id::create("mem");
    endfunction: new
   
endclass : obi_cntxt