// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `coverage_in` para verificação UVM do multiplicador binário de 32x32 bits
//             - Coleta cobertura funcional das entradas do DUT, como operandos e sinal de controle.
//             - Verifica a variação dos valores de entrada, garantindo a cobertura de todos os cenários possíveis.
//             - Utiliza bins para cobrir diferentes combinações de multiplicandos (32x32 bits) e sinais de controle.
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------
class coverage_in extends bvm_cover #(tr_in);
   `uvm_component_utils(coverage_in)

   covergroup transaction_covergroup;  // predefined name of covergroup
      option.per_instance = 1;
      
      cp_a: coverpoint coverage_transaction.a {
        bins a_0            = {32'h0};
        bins a_1            = {32'h1};
        bins a_max          = {32'hFFFFFFFF};
        bins a_medium[100]  = {[32'h00000010:32'hFFFFFFEF]}; 
        option.at_least = 10;   
      }

      cp_a_high_low: coverpoint coverage_transaction.a {
        bins a_low          = {[32'h00000000:32'h0000000F]};
        bins a_high         = {[32'hFFFFFFF0:32'hFFFFFFFF]};
        option.at_least = 10;  
      }

      cp_b: coverpoint coverage_transaction.b {
        bins b_0       = {32'h0};
        bins b_1       = {32'h1};
        bins b_max     = {32'hFFFFFFFF};
        bins b_medium[100]  = {[32'h00000010:32'hFFFFFFEF]};
        option.at_least = 10;
      }

      cp_b_high_low:coverpoint coverage_transaction.b {
        bins b_low    = {[32'h00000000:32'h0000000F]};
        bins b_high   = {[32'hFFFFFFF0:32'hFFFFFFFF]};
      }

      cp_op_sel: coverpoint coverage_transaction.op_sel {
        bins bin0[] = {[0:3]};
      }

      mult_cross1: cross cp_b_high_low, cp_op_sel {
        option.at_least = 10;
      }
 
   endgroup
   `bvm_cover_utils(tr_in)
    
endclass : coverage_in

