class a_tr extends uvm_sequence_item;

  rand int a;

  constraint a_positive { a > 0; }
  constraint a_small { a < 20; }

  `uvm_object_utils_begin(a_tr)  // needed for transaction recording
     `uvm_field_int(a, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

