class a_tr extends uvm_sequence_item;
  
  rand int c;
 
  `uvm_object_utils_begin(a_tr)  // needed for transaction recording
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

class apb_tr extends uvm_sequence_item;


  rand int divisor, dividendo;

  /*                // in case of read operation, data which have been read
  constraint dividendo_positive { dividendo > 100; }
  constraint dividendo_small { dividendo < 200; } 

 constraint divisor_positive { divisor > 10; }
  constraint divisor_small { divisor < 20; } */

  `uvm_object_utils_begin(apb_tr) // needed for transaction recording
     `uvm_field_int(divisor, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(dividendo, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

