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
     a_vi.valid <= 'x;
     a_vi.a  <= 'x;   
     fork // reset may occur at any time, therefore let's treat is in a separate task
       reset_signals();
       get_and_drive();
     join
   endtask

   task reset_signals();
      forever begin
         wait (a_vi.reset === 1);
         a_vi.valid <= 0;
         a_vi.a  <= 'x;   
         @(negedge a_vi.reset);
      end
   endtask

   task get_and_drive();
      a_tr tr_sequencer; // transaction coming from sequencer

      forever begin
          wait (a_vi.reset === 0);
         
          seq_item_port.get_next_item(tr_sequencer); // get transaction

          // wiggle interface signals
          @(posedge a_vi.clock);
          a_vi.valid <= 1;
          a_vi.a <= tr_sequencer.a;

          seq_item_port.item_done(); // notify sequencer that transaction is completed

          @(posedge a_vi.clock);
          a_vi.valid <= 0;
          @(posedge a_vi.clock);

        end
   endtask

endclass

