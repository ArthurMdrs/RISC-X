// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `monitor` para verificação UVM do multiplicador binário de 32x32 bits
//             - Captura e observa sinais do DUT.
//             - Converte sinais de back-to-back em transações UVM para o scoreboard.
//             - Verifica aderência ao protocolo de handshake e sequencialidade das operações.
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------
//Monitor out
class monitor_out extends uvm_monitor;  
   `uvm_component_utils(monitor_out)

   uvm_analysis_port #(tr_out) out;
    
   virtual out_mult_if out_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual out_mult_if)::get(this, "", "out_vi", out_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      tr_out tr;
      forever begin
         wait (out_vi.reset === 0);
         tr = tr_out::type_id::create("tr");

         `bvm_begin_tr(tr)          // start transaction recording
         while (!(out_vi.out_valid_o === 1 && out_vi.out_ready_i === 1))
            @(posedge out_vi.clock);
            tr.c = out_vi.c;
            @(posedge out_vi.clock);
         `bvm_end_tr(tr)           // end transaction recording
         out.write(tr);
         
      end
   endtask

endclass : monitor_out

//Monitor in
class monitor_in extends uvm_monitor;  
   `uvm_component_utils(monitor_in)

   uvm_analysis_port #(tr_in) out;
    
   virtual in_mult_if in_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual in_mult_if)::get(this, "", "in_vi", in_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      tr_in tr;
      forever begin
         wait (in_vi.PRESETn === 1);
         tr = tr_in::type_id::create("tr");
         `bvm_begin_tr(tr)          // start transaction recording
         while (!(in_vi.in_ready_o === 1 && in_vi.in_valid_i === 1))
            @(posedge in_vi.PCLK);
            tr.a = in_vi.a;
            tr.b = in_vi.b;
            tr.op_sel = in_vi.op_sel;
            @(posedge in_vi.PCLK);
         `bvm_end_tr(tr)          // end transaction recording
         out.write(tr);
      end
   endtask

endclass : monitor_in

