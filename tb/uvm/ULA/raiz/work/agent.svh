class agent extends uvm_agent;
  `uvm_component_utils(agent)
    
   uvm_analysis_port #(a_tr) out;
    
   sequencer sequencer_h;
   driver_master driver_h;
   monitor monitor_h;

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     out = new("out", this);
     if(get_is_active() == UVM_ACTIVE) begin
        sequencer_h = sequencer::type_id::create("sequencer_h", this);
        driver_h = driver_master::type_id::create("driver_h", this);
     end
     monitor_h = monitor::type_id::create("monitor_h", this);
   endfunction

   function void connect_phase(uvm_phase phase);
     monitor_h.out.connect (out);
     if(get_is_active() == UVM_ACTIVE) begin
        driver_h.seq_item_port.connect( sequencer_h.seq_item_export );
     end
   endfunction
    
endclass

