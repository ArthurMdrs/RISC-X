class coverage_in extends bvm_cover #(tr_in);
   `uvm_component_utils(coverage_in)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.divisor { // coverage_transaction is predefined name of transaction instance
        bins divisor_low          = {[32'h00000000:32'h0000000F]};       
        bins divisor_high         = {[32'hFFFFFFF0:32'hFFFFFFFF]}; 
        //bins divisor_0            = {32'h0};
        bins divisor_1            = {32'h1};
        bins divisor_max          = {32'hFFFFFFFF};
        bins divisor_medium[100]  = {[32'h00000010:32'hFFFFFFEF]};        
        option.at_least = 10; 
      }

      coverpoint coverage_transaction.dividendo { // coverage_transaction is predefined name of transaction instance
        bins dividendo_low     = {[32'h00000000:32'h0000000F]}; 
        bins dividendo_high    = {[32'hFFFFFFF0:32'hFFFFFFFF]}; 
        bins dividendo_0       = {32'h0};
        bins dividendo_1       = {32'h1};
        bins dividendo_max     = {32'hFFFFFFFF};
        bins dividendo_medium[100]  = {[32'h00000010:32'hFFFFFFEF]};
        option.at_least = 10; 
      }
   endgroup
   `bvm_cover_utils(tr_in)
    
endclass : coverage_in

