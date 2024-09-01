class coverage_out extends bvm_cover #(a_tr);
   `uvm_component_utils(coverage_out)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.c { // coverage_transaction is predefined name of transaction instance
       // create one bin, for 0 and 1
        bins d2 = {[10:30]}; // create one bins, for 2, 3,...,20
         // at least 3 ocurrences in each bin
          option.at_least = 5000;
      }
      
    endgroup
   `bvm_cover_utils(a_tr)
    
endclass

