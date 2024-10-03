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
   logic [31:0] rem;
   logic signal;

   task run_phase (uvm_phase phase);
   
     tr_in tr_input;
     tr_out tr_output;
     
     forever begin
        in.get(tr_input);
         tr_output = tr_out::type_id::create("tr_output", this);	
          `bvm_begin_tr(tr_output)
          tr_output.aux = 0;

      if (tr_input.signal_division == 1)begin
        if (tr_input.divisor == '0) begin
            result = 2**32 - 1;
            rem = $signed(tr_input.dividendo);
            tr_output.c = result;
            tr_output.r = rem; 
            tr_output.aux = 1;
        end
        else if (tr_input.divisor == '1 && tr_input.dividendo == 1 << 31) begin
            result = -(2**31);
            rem = '0;
            tr_output.c = result;
            tr_output.r = rem   ;
            tr_output.aux = 2;
        end
        else begin
          if (tr_input.dividendo[31] && tr_input.divisor[31]) begin 
            result = $signed(tr_input.dividendo) / $signed(tr_input.divisor)      ;
            rem    = - ($signed(tr_input.dividendo) % $signed (tr_input.divisor)) ;
            tr_output.c = result;
            tr_output.r = rem;
            tr_output.aux = 3;
          end
          else begin
            result = $signed(tr_input.dividendo) / $signed(tr_input.divisor)  ;
            rem    = $signed(tr_input.dividendo) % $signed (tr_input.divisor) ;
            tr_output.c = result;
            tr_output.r = rem;
            tr_output.aux = 4;
          end
          end
        end
      else begin
        if (tr_input.divisor == '0) begin
            result = 2**32 - 1;
            rem    = tr_input.dividendo;
            tr_output.c = result;
            tr_output.r = rem;
            tr_output.aux = 5;
        end
        else begin
            result = (tr_input.dividendo) / (tr_input.divisor);
            rem    = (tr_input.dividendo) % (tr_input.divisor);
            tr_output.c = result;
            tr_output.r = rem;
            tr_output.aux = 6;
        end
      end
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

