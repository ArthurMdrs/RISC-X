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

