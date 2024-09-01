class driver_master extends uvm_driver #(a_tr);
  `uvm_component_utils(driver_master)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   // a virtual interface must be substituted later with an actual interface instance
   virtual a_if a_vi; 

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     // get interface instance from database
     assert( uvm_config_db #(virtual a_if)::get(this, "", "a_vi", a_vi) );
   endfunction

   task run_phase(uvm_phase phase);  
    
     a_vi.out_ready_i <= 0;
    
     fork // reset may occur at any time, therefore let's treat is in a separate task
       reset_signals();
       get_and_drive();
     join
   endtask

   task reset_signals();
      forever begin
         wait (a_vi.reset === 1);

         a_vi.out_ready_i <= 0;

        wait (a_vi.reset === 0);
      end
  endtask

   task get_and_drive();
      a_tr tr_sequencer; // transaction coming from sequencer

      forever begin
        
         wait (a_vi.reset === 0);
         
         //seq_item_port.get_next_item(tr_sequencer); // get transaction

         a_vi.out_ready_i = 1;
        
      @(posedge a_vi.clock);
        while (!(a_vi.out_valid_o === 1))
        //wait (a_vi.out_valid_o === 1);
        @(posedge a_vi.clock);
        a_vi.out_ready_i = 0;
      
        @(posedge a_vi.clock);
         //seq_item_port.item_done(); // notify sequencer that transaction is completed

      end
   endtask

endclass

///////////////////////////////////////////////////////////////////////////////////////////////////////////

class apb_driver_master extends uvm_driver #(apb_tr);
  `uvm_component_utils(apb_driver_master)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   // a virtual interface must be substituted later with an actual interface instance
   virtual apb_if apb_vi; 

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     // get interface instance from database
     assert( uvm_config_db #(virtual apb_if)::get(this, "", "apb_vi", apb_vi) );
   endfunction

   task run_phase(uvm_phase phase);

     apb_vi.divisor  <= 'x; 
     apb_vi.dividendo  <= 'x; 
     apb_vi.in_valid_i <= 'x; //Indica validade dos dados na interface de entrada
     apb_vi.in_ready_o <= 'x;

     fork // reset may occur at any time, therefore let's treat is in a separate task
       reset_signals();
       get_and_drive();
     join
   endtask

   task reset_signals();
      forever begin
         wait (apb_vi.PRESETn === 0);
         apb_vi.divisor     <= 0; 
         apb_vi.dividendo   <= 0; 
         apb_vi.in_valid_i  <= 0; //Indica validade dos dados na interface de entrada
         

         @(posedge apb_vi.PRESETn);
      end
   endtask

   task get_and_drive();

      apb_tr tr_sequencer; // transaction coming from sequencer
      // Forking a process to randomly toggle in_valid_i and out_ready
/*
    fork

      forever begin
      // Random delay before each toggle
      #(5 + $urandom_range(0, 10)); // Random delay between 5 and 15 time units
      apb_vi.in_valid_i <= $urandom_range(0, 1);
      end

    join_none*/

      forever begin
        wait (apb_vi.PRESETn === 1);
  
        seq_item_port.get_next_item(tr_sequencer); // get transaction
        
        apb_vi.in_valid_i <= 1;
     
        apb_vi.dividendo  <= tr_sequencer.dividendo; 
        apb_vi.divisor    <= tr_sequencer.divisor;
  @(posedge apb_vi.PCLK);
        // Keep in_valid_i high until ready goes low
        @(posedge apb_vi.PCLK);
        wait (apb_vi.in_ready_o === 1); 
        apb_vi.in_valid_i = 0;

        seq_item_port.item_done(); // notify sequencer that transaction is completed
      end
   endtask

endclass

/*
Quero que dentro do forever os dados iniciem in_valid_i = 1 depois de 10 pulsos de clock e se mantenha constante até que o ready for 0, para cada borda positiva do clock.
Também que o out_ready se iniciei em 1 e se matenha constante ate que oub_valid for igual a zero.

Coloque essa lógica dentro do forever, pode apagar o que achar pertinente. Menos a linha wait... e seq_item_port.item_done. A linguagem é sytemverilog e também esse arquivo é o driver de uvm
*/
//TRansações apnes com out_READY = 1 ;

// A comparação do dut com ref mod deve ser quando o out_valid/out_valid_o/valid0

