
// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `refmod` para verificação UVM do multiplicador binário de 32x32 bits
//             - Compara a saída observada do DUT com os resultados esperados.
//             - Calcula valores de referência com base no algoritmo de multiplicação de Booth.
//             - Verifica precisão dos cálculos parciais e do resultado final.
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------
class refmod extends uvm_component;
   `uvm_component_utils(refmod)
   uvm_get_port #(tr_in) in;
   uvm_blocking_put_port #(tr_out) out; 

   function new(string name, uvm_component parent=null);
      super.new(name,parent);
      in  = new("in",  this);
   endfunction : new

   virtual function void build_phase (uvm_phase phase);
   super.build_phase(phase);
        out = new("out", this);
   endfunction

   int m_matches, m_mismatches; 
   int register_file;
   int result;
   task run_phase (uvm_phase phase);

     tr_in tr_input;
     tr_out tr_output;

     forever begin
        in.get(tr_input);
         tr_output = tr_out::type_id::create("tr_output", this);	
          `bvm_begin_tr(tr_output)
       // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU

          if      (tr_input.op_sel == 1) begin //  MULH = 
            resul = 
          end
          else if (tr_input.op_sel == 2) begin  // MULHSU
            result = 
          end
          else if (tr_input.op_sel == 3) begin  // MULHU
            result = 
          end
          else begin                           //  MUL = MULT COM SINAL
            result =  tr_input.b * tr_input.a; 
          end

         tr_output.c = result;

          out.put(tr_output);
          `bvm_end_tr(tr_output)
        end
  endtask

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(),
              $sformatf("%d matches, %d mismatches", m_matches, m_mismatches),
              UVM_NONE)
  endfunction

endclass : refmod

