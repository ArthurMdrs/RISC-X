//Transaction Out
class a_tr extends uvm_sequence_item;
  
  rand int c;
 
  `uvm_object_utils_begin(a_tr)  // needed for transaction recording
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

//Transaction In

class apb_tr extends uvm_sequence_item;

  rand int divisor, dividendo;

  function new(string name = "apb_tr");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(apb_tr) // needed for transaction recording
     `uvm_field_int(divisor, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(dividendo, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

endclass

//Transaction Item for Constraint, class derivate apb_tr 
//Case underlfow = Dividendo baixo e divisor baixo;

class item extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item)
  `uvm_object_utils_end

  //Constructor
  function new(string name = "item");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
	constraint c1 { soft divisor inside   {[32'h00000000:32'h0000000F]};}
  constraint c2 { soft dividendo inside {[32'h00000000:32'h0000000F]};}

endclass

//Case Overlfow = Dividendo baixo e divisor baixo;

class item2 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item2)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item2");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo

	 constraint c3 { soft divisor inside   {[32'hFFFFFF00:32'hFFFFFFFF]};}
   constraint c4 { soft dividendo inside {[32'hFFFFFF00:32'hFFFFFFFF]};}

endclass

//Case dividendo = 0; 

class item3 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item3)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item3");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
	constraint c5 { soft dividendo inside   {0};}
  constraint c6 { soft divisor inside   {[32'h00000000:32'hFFFFFFFF]};}

endclass

//Case divisor = 0;

class item4 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item4)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item4");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
	constraint c7 { soft dividendo inside {[32'h00000000:32'hFFFFFFFF]};}
  constraint c8 { soft divisor inside   {0};}
endclass

//Case dividendo = 1;

class item5 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item5)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item5");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
  constraint c2 { soft dividendo inside   {1};}
  constraint c1 { soft divisor inside   {[32'h00000000:32'hFFFFFFFF]};}

endclass

//Case divisor = 1;

class item6 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item6)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item6");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
  constraint c2 {soft dividendo inside   {[32'h00000000:32'hFFFFFFFF]};}
  constraint c1 { soft divisor inside   {1};}

endclass

class item7 extends apb_tr;

///Utility and Field macros,
  `uvm_object_utils_begin(item7)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item7");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo

  constraint c3 { soft divisor inside   {32'h0};}
  constraint c4 { soft dividendo inside {32'h0};}

endclass