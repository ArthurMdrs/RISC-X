// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `driver` para verificação UVM do multiplicador binário de 32x32 bits
//             - Recebe as transações do sequencer.
//             - Converte transações UVM em estímulos de sinal (estímulo do handshake e dados).
//             - Usa lógica de controle baseada no protocolo (valid e ready).
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------
//Driver out
class driver_out extends uvm_driver #(tr_out);
  `uvm_component_utils(driver_out)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   // a virtual interface must be substituted later with an actual interface instance
   virtual out_mult_if out_vi; 

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     // get interface instance from database
     assert( uvm_config_db #(virtual out_mult_if)::get(this, "", "out_vi", out_vi) );
   endfunction

   task run_phase(uvm_phase phase);  
    
     out_vi.out_ready_i <= 0;
    
     fork // reset may occur at any time, therefore let's treat is in a separate task
       reset_signals();
       get_and_drive();
     join
   endtask

   task reset_signals();
      forever begin
         wait (out_vi.reset === 1);
          out_vi.out_ready_i <= 0;
         wait (out_vi.reset === 0);
      end
  endtask

   task get_and_drive();
      tr_out tr_sequencer; // transaction coming from sequencer

      forever begin
        
         wait (out_vi.reset === 0);
         out_vi.out_ready_i = 1; 
        @(posedge out_vi.clock);
        while (!(out_vi.out_valid_o === 1))
        @(posedge out_vi.clock);
        out_vi.out_ready_i = 0;
        @(posedge out_vi.clock);

      end
   endtask

endclass : driver_out

//Driver In
class driver_in extends uvm_driver #(tr_in);
  `uvm_component_utils(driver_in)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   // a virtual interface must be substituted later with an actual interface instance
   virtual in_mult_if in_vi; 

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     // get interface instance from database
     assert( uvm_config_db #(virtual in_mult_if)::get(this, "", "in_vi", in_vi) );
   endfunction

   task run_phase(uvm_phase phase);

     in_vi.a          <= 'x; 
     in_vi.b          <= 'x; 
     in_vi.in_valid_i <= 'x; 
     in_vi.in_ready_o <= 'x;
     in_vi.op_sel     <= 'x;

     fork // reset may occur at any time, therefore let's treat is in a separate task
       reset_signals();
       get_and_drive();
     join
   endtask

   task reset_signals();
      forever begin
         wait (in_vi.PRESETn === 0);
         in_vi.a           <= 0; 
         in_vi.b           <= 0; 
         in_vi.in_valid_i  <= 0;
         in_vi.op_sel      <= 0; 
         @(posedge in_vi.PRESETn);
      end
   endtask

   task get_and_drive();

      tr_in tr_sequencer; // transaction coming from sequencer

      forever begin
        wait (in_vi.PRESETn === 1);
        seq_item_port.get_next_item(tr_sequencer); // get transaction
        in_vi.in_valid_i <= 1;
        in_vi.op_sel <= 1;
         #10 in_vi.in_valid_i <= 0;
        in_vi.b  <= tr_sequencer.b; 
        in_vi.a    <= tr_sequencer.a;
      //`uvm_info("IN DRV", $sformatf("\n*************************\nDriving tr:\n%s\n*************************", tr_sequencer.convert2string()), UVM_HIGH)
        @(posedge in_vi.PCLK);
        @(posedge in_vi.PCLK);
        wait (in_vi.in_ready_o === 1); 
        in_vi.in_valid_i = 0;
        seq_item_port.item_done(); // notify sequencer that transaction is completed
      end
   endtask

endclass : driver_in


