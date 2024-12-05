class agent_div_out extends uvm_agent;
  `uvm_component_utils(agent_div_out)
    
   uvm_analysis_port #(tr_out) out;
    
   out_sequencer sequencer_h;
   driver_div_out driver_h;
   monitor_div_out monitor_h;

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     out = new("out", this);
     if(get_is_active() == UVM_ACTIVE) begin
        sequencer_h = out_sequencer::type_id::create("sequencer_h", this);
        driver_h = driver_div_out::type_id::create("driver_h", this);
     end
     monitor_h = monitor_div_out::type_id::create("monitor_h", this);
   endfunction

   function void connect_phase(uvm_phase phase);
     monitor_h.out.connect (out);
     if(get_is_active() == UVM_ACTIVE) begin
        driver_h.seq_item_port.connect( sequencer_h.seq_item_export );
     end
   endfunction
    
endclass : agent_div_out

class agent_div_in extends uvm_agent;
  `uvm_component_utils(agent_div_in)
    
   uvm_analysis_port #(tr_in) out;

   in_sequencer sequencer_h;
   driver_div_in driver_h;
   monitor_div_in monitor_h;

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     out = new("out", this);
     if(get_is_active() == UVM_ACTIVE) begin
        sequencer_h = in_sequencer::type_id::create("sequencer_h", this);
        driver_h    = driver_div_in::type_id::create("driver_h", this);
     end
     monitor_h      = monitor_div_in::type_id::create("monitor_h", this);
   endfunction

   function void connect_phase(uvm_phase phase);
     monitor_h.out.connect (out);
     if(get_is_active() == UVM_ACTIVE) begin
        driver_h.seq_item_port.connect( sequencer_h.seq_item_export );
     end
   endfunction
    
endclass : agent_div_in

