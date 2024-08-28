class obi_tr #(int XLEN=32, int ALEN=32) extends uvm_sequence_item;
    
    // Number of cycles for arrival of gnt and rvalid
    rand int gnt_latency;
    rand int rvalid_latency;
    
    // Address phase signals
    logic [ALEN  -1:0] addr;
    logic              we;
    logic [XLEN/8-1:0] be;
    logic [XLEN  -1:0] wdata;
    
    // Response phase signals
    rand logic [XLEN  -1:0] rdata;
    
    int id;

    `uvm_object_param_utils_begin(obi_tr)
        `uvm_field_int(gnt_latency, UVM_ALL_ON)
        `uvm_field_int(rvalid_latency, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
        `uvm_field_int(be, UVM_ALL_ON)
        `uvm_field_int(wdata, UVM_ALL_ON)
        `uvm_field_int(rdata, UVM_ALL_ON)
        `uvm_field_int(id, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="obi_tr");
        super.new(name);
    endfunction: new

    constraint valid_gnt_latency { 
        gnt_latency >= 0;
        gnt_latency <= 10;
    }
    constraint valid_rvalid_latency { 
        rvalid_latency >= 0;
        rvalid_latency <= 10;
    }

    function string convert2string();
        string string_aux;

        string_aux = {string_aux, "\n***************************\n"};
        string_aux = {string_aux, $sformatf("** gnt_latency value: %0d\n", gnt_latency)};
        string_aux = {string_aux, $sformatf("** rvalid_latency value: %0d\n", rvalid_latency)};
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

endclass: obi_tr

class obi_no_wait_tr extends obi_tr;
  
    `uvm_object_param_utils(obi_no_wait_tr)

    constraint no_gnt_latency { 
        gnt_latency == 0;
    }

    constraint no_rvalid_latency { 
        rvalid_latency == 0;
    }
  
    function new (string name = "obi_tr");
        super.new (name);
    endfunction
    
endclass : obi_no_wait_tr
