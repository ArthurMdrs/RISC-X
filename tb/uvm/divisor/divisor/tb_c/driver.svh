//Driver out
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
        @(posedge a_vi.clock);
        a_vi.out_ready_i = 0;
        @(posedge a_vi.clock);
         //seq_item_port.item_done(); // notify sequencer that transaction is completed

      end
   endtask

endclass

//Driver In
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

      forever begin
        wait (apb_vi.PRESETn === 1);
        seq_item_port.get_next_item(tr_sequencer); // get transaction
      
        // Old
        apb_vi.in_valid_i <= 1;

        // New
        // apb_vi.in_valid_i <= 1;
        
        `uvm_info("IN DRV", $sformatf("\n*************************\nDriving tr:\n%s\n*************************", tr_sequencer.convert2string()), UVM_HIGH)

        apb_vi.dividendo  <= tr_sequencer.dividendo; 
        apb_vi.divisor    <= tr_sequencer.divisor;
        
        while (apb_vi.in_ready_o !== 1)
            @(posedge apb_vi.PCLK);
        
        @(posedge apb_vi.PCLK);
        apb_vi.in_valid_i <= 0;

        seq_item_port.item_done(); // notify sequencer that transaction is completed
      end
   endtask

endclass


