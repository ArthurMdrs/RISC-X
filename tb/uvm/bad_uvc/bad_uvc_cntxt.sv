class bad_uvc_cntxt #(int XLEN=32, int ALEN=32) extends uvm_object;

    riscx_mem_model mem;

    bad_uvc_reset_state_enum rst_state = BAD_UVC_RST_STATE_PRE_RESET;
   
    `uvm_object_utils_begin(bad_uvc_cntxt)
        `uvm_field_enum(bad_uvc_reset_state_enum, rst_state, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "bad_uvc_cntxt");
        super.new(name);
        
        mem = riscx_mem_model#(ALEN)::type_id::create("mem");
    endfunction: new
   
endclass : bad_uvc_cntxt