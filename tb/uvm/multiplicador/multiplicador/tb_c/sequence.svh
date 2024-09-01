class a_sequence extends uvm_sequence #(a_tr);
    `uvm_object_utils(a_sequence)
    
    function new (string name = "a_sequence");
      super.new(name);
    endfunction: new

    task body;
      a_tr tr;

      forever begin
        `uvm_do(tr)
      end
    endtask
   
endclass

class apb_sequence extends uvm_sequence #(apb_tr);
    `uvm_object_utils(apb_sequence)
    
    function new (string name = "apb_sequence");
      super.new(name);
    endfunction: new

    task body;
      apb_tr tr;

      forever begin
        `uvm_do(tr)
      end
    endtask
   
endclass

