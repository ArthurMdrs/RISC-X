//Transaction Out - a_tr
class tr_out extends uvm_sequence_item;
  
  rand logic [31:0] c;
  rand logic [31:0] r;
  int aux;

 
  `uvm_object_utils_begin(tr_out)  // needed for transaction recording
     `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(r, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(aux, UVM_ALL_ON | UVM_DEC | UVM_NOCOMPARE)
  `uvm_object_utils_end

function string convert2string();
    return $sformatf("Resultado = 32'h%h", c);
    return $sformatf("Resultado = 32'h%h", r);
endfunction


endclass : tr_out

//Transaction In apb_tr
class tr_in extends uvm_sequence_item;

  rand logic [31:0] divisor, dividendo;
  rand bit signal_division;

  function new(string name = "tr_in");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(tr_in) // needed for transaction recording
     `uvm_field_int(dividendo, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(divisor, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(signal_division, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end
  
  //constraint non_zero_divisor { divisor != 32'b0;}
  //constraint signal_division_positive { signal_division == 0;}
  constraint signal_division_small { signal_division == 1; }
  

function string convert2string();
    string my_str;
    if (signal_division)
        my_str = {$sformatf("divisor = 32'h%h\ndividendo = 32'h%h\n", divisor, dividendo), 
                  $sformatf("divisor = %0d\ndividendo = %0d\n", $signed(divisor), $signed(dividendo)),
                  $sformatf("signed division")};
    else
        my_str = {$sformatf("divisor = 32'h%h\ndividendo = 32'h%h\n", divisor, dividendo), 
                  $sformatf("divisor = %0d\ndividendo = %0d\n", $unsigned(divisor), $unsigned(dividendo)),
                  $sformatf("UNsigned division")};
    return my_str;
endfunction

endclass : tr_in

//Case underlfow = Dividendo baixo e divisor baixo;

class item extends tr_in;

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

endclass : item

//Case Overlfow = Dividendo baixo e divisor baixo;

class item2 extends tr_in;

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

endclass : item2

//Case dividendo = 0; 

class item3 extends tr_in;

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

endclass : item3

//Case divisor = 0;

class item4 extends tr_in;

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
endclass : item4

//Case dividendo = 1;

class item5 extends tr_in;

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

endclass : item5

//Case divisor = 1;

class item6 extends tr_in;

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

endclass : item6

class item7 extends tr_in;

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

endclass : item7

/*class item8 extends tr_in;

///Utility and Field macros,
  `uvm_object_utils_begin(item7)

  `uvm_object_utils_end

  //Constructor
  function new(string name = "item7");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
                                        
  constraint c9 { soft divisor inside   {32'hFFFFFFFF};}
  constraint c10{ soft dividendo inside {32'h80000000};}

endclass : item8
*/