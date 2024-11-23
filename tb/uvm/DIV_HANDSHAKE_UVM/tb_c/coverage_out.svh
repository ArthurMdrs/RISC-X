class coverage_out extends bvm_cover #(tr_out);
   `uvm_component_utils(coverage_out)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.c { // coverage_transaction is predefined name of transaction instance
        bins valor_zero = {0};                        // Resultado igual a 0
        bins valor_positivo[100] = {[1:32'h7FFFFFFF]};     // Intervalo de resultados positivos
        bins valor_negativo[100] = {[32'h80000000:32'hFFFFFFFF]}; // Intervalo de resultados negativos
        option.at_least = 10;
      }
    endgroup
   `bvm_cover_utils(tr_out)
    
endclass : coverage_out