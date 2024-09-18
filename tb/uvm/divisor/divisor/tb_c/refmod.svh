class refmod extends uvm_component;
   `uvm_component_utils(refmod)

   // The functionality of this refmod is meaningless. It only demonstrates APB transaction
   // and event transaction.

   uvm_get_port #(apb_tr) in;
   uvm_blocking_put_port #(a_tr) out; 

   function new(string name, uvm_component parent=null);
      super.new(name,parent);
      in  = new("in",  this);
      
   endfunction : new


   virtual function void build_phase (uvm_phase phase);
   super.build_phase(phase);
        out = new("out", this);

   endfunction

   // a register file for APB interaction
   int m_matches, m_mismatches; // used for APB read operations
   int register_file;
//    int  result;
   logic [31:0]  result;
   task run_phase (uvm_phase phase);
   
     apb_tr tr_in;
     a_tr tr_out;


     forever begin
        in.get(tr_in);
       
         tr_out = a_tr::type_id::create("tr_out", this);	
          `bvm_begin_tr(tr_out)
        //    result =  tr_in.dividendo / tr_in.divisor;
        if (tr_in.divisor == '0) begin
            result = 2**32 - 1;
        end
        else if (tr_in.divisor == '1 && tr_in.dividendo == 2**32 - 1) begin
            result = -(2**31);
        end
        else begin
            result = $signed(tr_in.dividendo) / $signed(tr_in.divisor);
        end
           tr_out.c = result;
          out.put(tr_out);
          `bvm_end_tr(tr_out)
        end
    
  endtask

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(),
              $sformatf("%d matches, %d mismatches", m_matches, m_mismatches),
              UVM_NONE)
  endfunction

endclass

