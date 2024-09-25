//Monitor OUT
class monitor_div_out extends uvm_monitor;  
   `uvm_component_utils(monitor_div_out)
   uvm_analysis_port #(tr_out) out;
   virtual out_div_if out_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual out_div_if)::get(this, "", "out_vi", out_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      tr_out tr;
      forever begin
         wait (out_vi.reset === 0);
         tr = tr_out::type_id::create("tr");
         `bvm_begin_tr(tr)          // start transaction recording

         while (!(out_vi.out_valid_o === 1 && out_vi.out_ready_i === 1)) begin
            @(posedge out_vi.clock);
         end
        tr.c = out_vi.c;
        @(posedge out_vi.clock);
        `uvm_info("OUT MON", $sformatf("\n*************************\nCollected tr:\n%s\n*************************", tr.convert2string()), UVM_MEDIUM)
         out.write(tr);
         `bvm_end_tr(tr)           // end transaction recording
      end
   endtask

endclass : monitor_div_out

//Monitor In
class monitor_div_in extends uvm_monitor;  
   `uvm_component_utils(monitor_div_in)
   uvm_analysis_port #(tr_in) out;
   virtual in_div_if in_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual in_div_if)::get(this, "", "in_vi", in_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      tr_in tr;
      forever begin
         wait (in_vi.PRESETn === 1);
         tr = tr_in::type_id::create("tr");
         `bvm_begin_tr(tr) // start transaction recording
         while (!(in_vi.in_ready_o === 1 && in_vi.in_valid_i === 1))
            @(posedge in_vi.PCLK);
            tr.divisor = in_vi.divisor;
            tr.dividendo = in_vi.dividendo;        
        `uvm_info("IN MON", $sformatf("\n*************************\nCollected tr:\n%s\n*************************", tr.convert2string()), UVM_MEDIUM)
         @(posedge in_vi.PCLK);
         out.write(tr);
         `bvm_end_tr(tr) // end transaction recording
      end
   endtask

endclass : monitor_div_in

