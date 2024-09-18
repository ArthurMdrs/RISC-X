//Monitor OUT
class monitor extends uvm_monitor;  
   `uvm_component_utils(monitor)

   uvm_analysis_port #(a_tr) out;
    
   virtual a_if a_vi; 
  

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual a_if)::get(this, "", "a_vi", a_vi) );
      
   endfunction
   
   task run_phase(uvm_phase phase);
      a_tr tr;
      forever begin
         wait (a_vi.reset === 0);
         tr = a_tr::type_id::create("tr");

         `bvm_begin_tr(tr)          // start transaction recording
         while (!(a_vi.out_valid_o === 1 && a_vi.out_ready_i === 1)) begin
            @(posedge a_vi.clock);
        // `uvm_info("OUT MON", $sformatf("\ntime = %t\t\t\tDEBUG", $realtime), UVM_NONE)
         end
        tr.c = a_vi.c;
        @(posedge a_vi.clock);

        `uvm_info("OUT MON", $sformatf("\n*************************\nCollected tr:\n%s\n*************************", tr.convert2string()), UVM_NONE)
         out.write(tr);
         `bvm_end_tr(tr)           // end transaction recording
         
      end
   endtask

endclass

//Monitor In
class apb_monitor extends uvm_monitor;  
   `uvm_component_utils(apb_monitor)

   uvm_analysis_port #(apb_tr) out;
    
   virtual apb_if apb_vi; 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      out = new("out", this);
   endfunction: new
    
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      assert( uvm_config_db #(virtual apb_if)::get(this, "", "apb_vi", apb_vi) );
   endfunction
   
   task run_phase(uvm_phase phase);
      apb_tr tr;
      forever begin
         wait (apb_vi.PRESETn === 1);

         tr = apb_tr::type_id::create("tr");
   
         `bvm_begin_tr(tr) // start transaction recording
         while (!(apb_vi.in_ready_o === 1 && apb_vi.in_valid_i === 1))
            @(posedge apb_vi.PCLK);
            tr.divisor = apb_vi.divisor;
            tr.dividendo = apb_vi.dividendo;        
        // `uvm_info("IN MON", $sformatf("\n*************************\nCollected tr:\n%s\n*************************", tr.convert2string()), UVM_NONE)
        // `uvm_info("IN MON", $sformatf("\n\ndivisor = 32'h%h\ndividendo = 32'h%h\n\n", apb_vi.divisor, apb_vi.dividendo), UVM_NONE)
            @(posedge apb_vi.PCLK);
        `uvm_info("IN MON", $sformatf("\n*************************\nCollected tr:\n%s\n*************************", tr.convert2string()), UVM_NONE)
         out.write(tr);
         `bvm_end_tr(tr) // end transaction recording
      end
   endtask

endclass

