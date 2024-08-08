class a_tr extends uvm_sequence_item;

  rand int a, b, c;

  constraint a_positive { a > 0; }
  constraint a_small { a < 1000; }

  constraint b_positive { b > 0; }
  constraint b_small { b < 5; }

  `uvm_object_utils_begin(a_tr)  // needed for transaction recording
     `uvm_field_int(a, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(b, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

