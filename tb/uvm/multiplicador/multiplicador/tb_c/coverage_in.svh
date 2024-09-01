/*class coverage_in extends bvm_cover #(a_tr);
   `uvm_component_utils(coverage_in)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.c { // coverage_transaction is predefined name of transaction instance
        bins d1 = {[0:1]}; // create one bin, for 0 and 1
        bins d2 = {[2:20]}; // create one bins, for 2, 3,...,20
        option.at_least = 3;  // at least 3 ocurrences in each bin
      }
   endgroup
   `bvm_cover_utils(a_tr)
    
endclass*/

class apb_coverage_in extends bvm_cover #(apb_tr);
   `uvm_component_utils(apb_coverage_in)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.divisor { // coverage_transaction is predefined name of transaction instance
       // create one bin, for 0 and 1
        bins d2 = {[2:20]}; // create one bins, for 2, 3,...,20
         // at least 3 ocurrences in each bin
      }
   endgroup
   `bvm_cover_utils(apb_tr)
    
endclass

