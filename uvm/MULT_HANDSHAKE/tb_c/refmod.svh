
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
   logic result;
   // int = 32b; logic = 64;
   task run_phase (uvm_phase phase);

     tr_in tr_input;
     tr_out tr_output;

     forever begin
        in.get(tr_input);
         tr_output = tr_out::type_id::create("tr_output", this);	
          `bvm_begin_tr(tr_output)
       // Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU
       //2'b00:MUL: Multiplicação normal (32 bits menos significativos). 
       //2'b01:MULH: Multiplicação com resultado na parte alta (32 bits mais significativos).
       //2'b10:MULHSU: Multiplicação com um operando com sinal e um sem sinal, resultado na parte alta. (32 bits mais significativos).
       //2'b11:MULHU: Multiplicação com dois operandos sem sinal, resultado na parte alta. (32 bits mais significativos).
       //lower_32 = in_data[31:0];   // Bits inferiores (0 a 31)
       //upper_32 = in_data[63:32]; // Bits superiores (32 a 63)

          if (tr_input.op_sel == 0) begin //  MUL = 
            result = (tr_input.b * tr_input.a);
            tr_output.c = result[31:0];
            tr_output.aux = 0;
          end
          else if (tr_input.op_sel == 1) begin  // MULH
            result = ($signed(tr_input.b) * $signed(tr_input.a)) << 4;
            tr_output.c = result[63:32];
            tr_output.aux = 1;
          end
          else if (tr_input.op_sel == 2) begin  // MULHSU
            result = $signed(tr_input.a) * $unsigned(tr_input.b);
            tr_output.c = result[63:32];
            tr_output.aux = 2;
          end
          else begin                           //  MULHU
            result =  $unsigned(tr_input.a) * $unsigned(tr_input.b);
            tr_output.c = result[63:32];
            tr_output.aux = 3;
          end

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

