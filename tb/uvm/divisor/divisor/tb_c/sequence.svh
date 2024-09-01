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
      int repeat_count = 10000; 
  // Iniciando transações específicas
        `uvm_info(get_type_name(), "Iniciando transações específicas", UVM_MEDIUM)

`uvm_info(get_type_name(), "Iniciando transações zero", UVM_MEDIUM)
       // Transação 1: Divisão por zero
        repeat (repeat_count) begin
            tr = apb_tr::type_id::create("tr");
            tr.dividendo = 32'h00000010;
            tr.divisor = 32'h00000000; // Divisor igual a zero
            `uvm_do(tr)
        end
`uvm_info(get_type_name(), "Iniciando transações um", UVM_MEDIUM)
        // Transação 2: Divisão por um
        repeat (repeat_count) begin
            tr = apb_tr::type_id::create("tr");
            tr.dividendo = 32'h00000010;
            tr.divisor = 32'h00000001; // Divisor igual a um
            `uvm_do(tr)
        end
`uvm_info(get_type_name(), "Iniciando transações igual", UVM_MEDIUM)
        // Transação 3: Dividendo igual ao divisor
        repeat (repeat_count) begin
            tr = apb_tr::type_id::create("tr");
            tr.dividendo = 32'h00000020;
            tr.divisor = 32'h00000020; // Dividendo igual ao divisor
            `uvm_do(tr)
        end

        // Transação 4: Dividendo negativo, divisor positivo
        repeat (repeat_count) begin
            tr = apb_tr::type_id::create("tr");
            tr.dividendo = 32'hFFFFFFF0; // Valor negativo
            tr.divisor = 32'h00000010;   // Valor positivo
            `uvm_do(tr)
        end

        // Transação 5: Dividendo e divisor negativos
        repeat (repeat_count) begin
            tr = apb_tr::type_id::create("tr");
            tr.dividendo = 32'hFFFFFFF0; // Valor negativo
            tr.divisor = 32'hFFFFFFF0;   // Valor negativo
            `uvm_do(tr)
        end
/*
        forever begin
            tr = apb_tr::type_id::create("tr");
            start_item(tr);
            tr.randomize();  // Gerar valores aleatórios
            finish_item(tr);
        end*/
    endtask
   
endclass

