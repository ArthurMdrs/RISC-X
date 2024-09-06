class bad_uvc_cfg #(int XLEN=32, int ALEN=32) extends uvm_object;

    uvm_active_passive_enum is_active;
    bad_uvc_cov_enable_enum cov_control;

    logic [ALEN-1:0] mem_start_addr = 1 << (ALEN-1);
    string mem_bin_file;
   
    `uvm_object_param_utils_begin(bad_uvc_cfg)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_enum(bad_uvc_cov_enable_enum, cov_control, UVM_ALL_ON)
        `uvm_field_int(mem_start_addr, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "bad_uvc_cfg");
        super.new(name);
        
        is_active = UVM_ACTIVE;
        cov_control = BAD_UVC_COV_ENABLE;
        
        if ($value$plusargs("start_addr=%h", mem_start_addr))
            `uvm_info("BAD_UVC CONFIG", $sformatf("Got memory start address from plusargs: 0x%h.", mem_start_addr), UVM_HIGH)
        // else
        //     `uvm_fatal("BAD_UVC CONFIG", $sformatf("%s %s", bin_file, error_desc))
        if ($value$plusargs("bin=%s", mem_bin_file))
            `uvm_info("BAD_UVC CONFIG", $sformatf("Got memory binary file path from plusargs: %s.", mem_bin_file), UVM_HIGH)
        else
            `uvm_fatal("BAD_UVC CONFIG", "A .bin file must be provided through plusargs!")
        
    endfunction: new
   
endclass : bad_uvc_cfg