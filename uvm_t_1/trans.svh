class a_tr extends uvm_sequence_item;

  rand int a, b, c;

  constraint a_positive { a > 0; }
  constraint a_small { a < 4294967; }

  constraint b_positive { b > 0; }
  constraint b_small { b < 429; }

  constraint c_positive { c > 0; }
  constraint c_small { c < 429295; }


  `uvm_object_utils_begin(a_tr)  // needed for transaction recording
     `uvm_field_int(a, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(b, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

