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
//Monitor in
class monitor extends uvm_monitor;  
   `uvm_component_utils(monitor)

   uvm_analysis_port #(a_tr) out;
    
   virtual a_if a_vi; 
  

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual a_if)::get(this, "", "a_vi", a_vi) );
      
   endfunction
   
   task run_phase(uvm_phase phase);
      a_tr tr;
      forever begin
         wait (a_vi.reset === 0);
         tr = a_tr::type_id::create("tr");

         `bvm_begin_tr(tr)          // start transaction recording
         while (!(a_vi.out_valid_o === 1 && a_vi.out_ready_i === 1))

            @(posedge a_vi.clock);
            tr.c = a_vi.c;
            @(posedge a_vi.clock);

         `bvm_end_tr(tr)           // end transaction recording
         out.write(tr);
         
      end
   endtask

endclass

//Monitor out
class apb_monitor extends uvm_monitor;  
   `uvm_component_utils(apb_monitor)

   uvm_analysis_port #(apb_tr) out;
    
   virtual apb_if apb_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual apb_if)::get(this, "", "apb_vi", apb_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      apb_tr tr;
      forever begin
         wait (apb_vi.PRESETn === 1);
         tr = apb_tr::type_id::create("tr");
         `bvm_begin_tr(tr)          // start transaction recording
         while (!(apb_vi.in_ready_o === 1 && apb_vi.in_valid_i === 1))

            @(posedge apb_vi.PCLK);
            tr.divisor = apb_vi.divisor;
            tr.dividendo = apb_vi.dividendo;
            @(posedge apb_vi.PCLK);

         `bvm_end_tr(tr)          // end transaction recording
         out.write(tr);
      end
   endtask

endclass

