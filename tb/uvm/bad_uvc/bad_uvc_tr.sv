class bad_uvc_tr #(int XLEN=32, int ALEN=32) extends uvm_sequence_item;
    
    // Address phase signals
    logic [ALEN  -1:0] addr;
    logic              we;
    logic [XLEN/8-1:0] be;
    logic [XLEN  -1:0] wdata;
    
    // Response phase signals
    rand logic [XLEN  -1:0] rdata;
    
    int id;

    `uvm_object_param_utils_begin(bad_uvc_tr)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
        `uvm_field_int(be, UVM_ALL_ON)
        `uvm_field_int(wdata, UVM_ALL_ON)
        `uvm_field_int(rdata, UVM_ALL_ON)
        `uvm_field_int(id, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="bad_uvc_tr");
        super.new(name);
    endfunction: new

    function string convert2string();
        string string_aux;

        string_aux = {string_aux, "\n***************************\n"};
        string_aux = {string_aux, $sformatf("** addr value: 0x%h\n", addr)};
        string_aux = {string_aux, $sformatf("** we value: %b\n", we)};
        string_aux = {string_aux, $sformatf("** be value: 0x%h\n", be)};
        string_aux = {string_aux, $sformatf("** wdata value: 0x%h\n", wdata)};
        string_aux = {string_aux, $sformatf("** rdata value: 0x%h\n", rdata)};
        string_aux = {string_aux, "***************************"};
        return string_aux;
    endfunction: convert2string

    // function void post_randomize();
    // endfunction: post_randomize

endclass: bad_uvc_tr
