class obi_tr #(int XLEN=32, int ALEN=32) extends uvm_sequence_item;
    
    // Number of cycles for arrival of gnt and rvalid
    rand int wait_gnt_cycles;
    rand int wait_rvalid_cycles;
    
    // Address phase signals
        //  logic              req;
        //  logic              gnt;
    rand logic [ALEN  -1:0] addr;
    rand logic              we;
    rand logic [XLEN/8-1:0] be;
    rand logic [XLEN  -1:0] wdata;
    
    // Response phase signals
        //  logic              rvalid;
        //  logic              rready;
    rand logic [XLEN  -1:0] rdata;

    `uvm_object_param_utils_begin(obi_tr)
        `uvm_field_int(wait_gnt_cycles, UVM_ALL_ON)
        `uvm_field_int(wait_rvalid_cycles, UVM_ALL_ON)
        // `uvm_field_int(req, UVM_ALL_ON)
        // `uvm_field_int(gnt, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(we, UVM_ALL_ON)
        `uvm_field_int(be, UVM_ALL_ON)
        `uvm_field_int(wdata, UVM_ALL_ON)
        // `uvm_field_int(rvalid, UVM_ALL_ON)
        // `uvm_field_int(rready, UVM_ALL_ON)
        `uvm_field_int(rdata, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="obi_tr");
        super.new(name);
    endfunction: new

    constraint valid_wait_gnt_cycles { 
        wait_gnt_cycles >= 0;
        wait_gnt_cycles <= 10;
    }
    constraint valid_wait_rvalid_cycles { 
        wait_rvalid_cycles >= 0;
        wait_rvalid_cycles <= 10;
    }

    function string convert2string();
        string string_aux;

        string_aux = {string_aux, "\n***************************\n"};
        string_aux = {string_aux, $sformatf("** wait_gnt_cycles value: %0d\n", wait_gnt_cycles)};
        string_aux = {string_aux, $sformatf("** wait_rvalid_cycles value: %0d\n", wait_rvalid_cycles)};
        // string_aux = {string_aux, $sformatf("** req value: 0x%h\n", req)};
        // string_aux = {string_aux, $sformatf("** gnt value: 0x%h\n", gnt)};
        string_aux = {string_aux, $sformatf("** addr value: 0x%h\n", addr)};
        string_aux = {string_aux, $sformatf("** we value: %b\n", we)};
        string_aux = {string_aux, $sformatf("** be value: 0x%h\n", be)};
        string_aux = {string_aux, $sformatf("** wdata value: 0x%h\n", wdata)};
        // string_aux = {string_aux, $sformatf("** rvalid value: 0x%h\n", rvalid)};
        // string_aux = {string_aux, $sformatf("** rready value: 0x%h\n", rready)};
        string_aux = {string_aux, $sformatf("** rdata value: 0x%h\n", rdata)};
        string_aux = {string_aux, "***************************"};
        return string_aux;
    endfunction: convert2string

    // function void post_randomize();
    // endfunction: post_randomize

endclass: obi_tr

class obi_no_wait_tr extends obi_tr;
  
    `uvm_object_param_utils(obi_no_wait_tr)

    constraint no_wait_gnt_cycles { 
        wait_gnt_cycles == 0;
    }

    constraint no_wait_rvalid_cycles { 
        wait_rvalid_cycles == 0;
    }
  
    function new (string name = "obi_tr");
        super.new (name);
    endfunction
    
endclass : obi_no_wait_tr
