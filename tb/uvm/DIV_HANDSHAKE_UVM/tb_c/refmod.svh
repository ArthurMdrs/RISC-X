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
   logic [31:0]  result;
   task run_phase (uvm_phase phase);
   
     tr_in tr_input;
     tr_out tr_output;
     
     forever begin
        in.get(tr_input);
         tr_output = tr_out::type_id::create("tr_out", this);	
          `bvm_begin_tr(tr_output)

        if (tr_input.divisor == '0) begin
            result = 2**32 - 1;
        end
        else if (tr_input.divisor == '1 && tr_input.dividendo == 2**32 - 1) begin
            result = -(2**31);
        end
        else begin
            result = $signed(tr_input.dividendo) / $signed(tr_input.divisor);
        end
           tr_output.c = result;
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

