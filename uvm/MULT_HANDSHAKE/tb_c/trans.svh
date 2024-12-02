//Transaction Out
class tr_out extends uvm_sequence_item;

  rand int c;
  int aux;

  `uvm_object_utils_begin(tr_out)  // needed for transaction recording
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(aux, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

  function string convert2string();
    return {$sformatf("Produto = 32'h%h\n", c)};
endfunction

endclass : tr_out

//Transaction In
class tr_in extends uvm_sequence_item;

  rand int a, b;
  int op_sel;

  function new(string name = "tr_in");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(tr_in) // needed for transaction recording
     `uvm_field_int(a, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(b, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(op_sel, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end


// Tipo de operação: 00=MUL, 01=MULH, 10=MULHSU, 11=MULHU
  constraint op_sel_MUL { op_sel == 0; }
//  constraint op_sel_MULH   {op_sel == 1;}
//  constraint op_sel_MULHSU {op_sel == 2;}
//  constraint op_sel_MULHU  {op_sel == 3;}
function string convert2string();
    string my_str;
    if (op_sel == 0) begin
        my_str = {$sformatf("A = 32'h%h\nB = 32'h%h\n", a, b), 
                  $sformatf("Fator = %0d\nFator2 = %0d\n", $signed(a), $signed(b)),
                  $sformatf("OP_SEL == 0 | MUL")};
    end else if (op_sel == 1) begin 
        my_str = {$sformatf("A = 32'h%h\nB = 32'h%h\n", a, b), 
                  $sformatf("Fator = %0d\nFator2 = %0d\n", $signed(a), $signed(b)),
                  $sformatf("OP_SEL == 2 | MUL")};
    end else if (op_sel == 2) begin 
        my_str = {$sformatf("A = 32'h%h\nB = 32'h%h\n", a, b), 
                  $sformatf("Fator = %0d\nFator2 = %0d\n", $signed(a), $signed(b)),
                  $sformatf("OP_SEL == 3 | MULHSU")};
    end else begin
        my_str = {$sformatf("A = 32'h%h\nB = 32'h%h\n", a, b), 
                  $sformatf("Fator = %0d\nFator2 = %0d\n", $signed(a), $signed(b)),
                  $sformatf("OP_SEL == 4 | MULHU")};
    end
    return my_str;
endfunction
  
endclass : tr_in

//Transaction Item for Constraint, class derivate tr_in 
//Case underlfow = b baixo e a baixo;

class item extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item)
  `uvm_object_utils_end

  //Constructor
  function new(string name = "item");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
	constraint c1 { soft a inside   {[32'h00000000:32'h0000000F]};}
  constraint c2 { soft b inside {[32'h00000000:32'h0000000F]};}
endclass : item

//Case Overlfow = b baixo e a baixo;

class item2 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item2)
  `uvm_object_utils_end

  //Constructor
  function new(string name = "item2");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
	 constraint c3 { soft a inside   {[32'hFFFFFF00:32'hFFFFFFFF]};}
   constraint c4 { soft b inside {[32'hFFFFFF00:32'hFFFFFFFF]};}
endclass : item2

//Case b = 0; 

class item3 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item3)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item3");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
	constraint c5 { soft b inside   {0};}
  constraint c6 { soft a inside   {[32'h00000000:32'hFFFFFFFF]};}
endclass : item3

//Case a = 0;

class item4 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item4)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item4");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
	constraint c7 { soft b inside {[32'h00000000:32'hFFFFFFFF]};}
  constraint c8 { soft a inside   {0};}
endclass : item4

//Case b = 1;

class item5 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item5)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item5");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
  constraint c2 { soft b inside   {1};}
  constraint c1 { soft a inside   {[32'h00000000:32'hFFFFFFFF]};}
endclass: item5

//Case a = 1;

class item6 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item6)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item6");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
  constraint c2 {soft b inside   {[32'h00000000:32'hFFFFFFFF]};}
  constraint c1 { soft a inside   {1};}
endclass : item6

class item7 extends tr_in;
  //Utility and Field macros,
  `uvm_object_utils_begin(item7)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item7");
    super.new(name);
  endfunction

  //Constraint, to generate any a and b
  constraint c3 { soft a inside   {32'h0};}
  constraint c4 { soft b inside {32'h0};}
endclass : item7