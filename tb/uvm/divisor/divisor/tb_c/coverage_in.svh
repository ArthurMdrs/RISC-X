

class apb_coverage_in extends bvm_cover #(apb_tr);
   `uvm_component_utils(apb_coverage_in)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      coverpoint coverage_transaction.divisor { // coverage_transaction is predefined name of transaction instance
        bins valor_zero = {0};  // Divisor igual a 0 (deve verificar exceções)
        bins valor_um = {1}; // Divisor igual a 1
        //bins valor_negativo = {[32'h80000000:32'hFFFFFFFF]};// Intervalo de valores negativos
        //bins valor_maximo = {32'hFFFFFFFF};// Divisor máximo possível
      //  bins valor_minimo = {32'h00000001};// Divisor mínimo possível, excluindo 0
      }

     /* coverpoint coverage_transaction.dividendo { // coverage_transaction is predefined name of transaction instance
        bins valor_zero = {0};// Dividendo igual a 0
        bins valor_um = {1};//Dividendo igual a 1
      //  bins valor_negativo = {[32'h80000000:32'hFFFFFFFF]};// Intervalo de valores negativos
       // bins valor_maximo = {32'hFFFFFFFF};//Dividendo máximo possível
        //bins valor_minimo = {32'h00000001};// Dividendo mínimo possível, excluindo 0
    
      }     // Cobertura de combinação entre dividendo e divisor/*
        cross coverage_transaction.dividendo , coverage_transaction.divisor {
        bins div_por_zero = binsof(coverage_transaction.divisor) intersect {0}; // Cenário de divisão por zero
        bins div_por_um = binsof(coverage_transaction.divisor) intersect {1};// Cenário de divisão por 1
    }*/

   endgroup
   `bvm_cover_utils(apb_tr)
    
endclass

