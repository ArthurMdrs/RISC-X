class div_base_test extends uvm_test;  
   `uvm_component_utils(div_base_test)

   env_div env_h;

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     env_h = env_div::type_id::create("env_h", this);
   endfunction

endclass : div_base_test

class div_signed_test extends div_base_test;  
   `uvm_component_utils(div_signed_test)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   task run_phase(uvm_phase phase);
     in_seq_signed seq;
     seq = in_seq_signed::type_id::create("seq");
     seq.start( env_h.agent_in_h.sequencer_h );
   endtask

endclass : div_signed_test

class div_unsigned_test extends div_base_test;  
   `uvm_component_utils(div_unsigned_test)

   function new(string name, uvm_component parent);
     super.new(name, parent);
   endfunction

   task run_phase(uvm_phase phase);
     in_seq_unsigned seq;
     seq = in_seq_unsigned::type_id::create("seq");
     seq.start( env_h.agent_in_h.sequencer_h );
   endtask

endclass : div_unsigned_test