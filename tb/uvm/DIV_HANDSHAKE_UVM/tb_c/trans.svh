//Transaction Out - a_tr
class tr_out extends uvm_sequence_item;
  
  rand logic [31:0] c;
  rand logic [31:0] r;
  int aux;

 
  `uvm_object_utils_begin(tr_out)  // needed for transaction recording
    //  `uvm_field_int(c, UVM_ALL_ON | UVM_DEC)
    //  `uvm_field_int(r, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(c, UVM_ALL_ON | UVM_HEX)
     `uvm_field_int(r, UVM_ALL_ON | UVM_HEX)
     `uvm_field_int(aux, UVM_ALL_ON | UVM_DEC | UVM_NOCOMPARE)
  `uvm_object_utils_end

function string convert2string();
    return {$sformatf("Quociente = 32'h%h\n", c),
            $sformatf("Resto     = 32'h%h", r)};
endfunction


endclass : tr_out

//Transaction In apb_tr
class tr_in extends uvm_sequence_item;

  rand logic [31:0] divisor, dividendo;
  rand bit signal_division;

  function new(string name = "tr_in");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(tr_in)
     `uvm_field_int(dividendo, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(divisor, UVM_ALL_ON | UVM_DEC)
     `uvm_field_int(signal_division, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

virtual function string convert2string();
    string my_str;
    if (signal_division)
        my_str = {
                    $sformatf("dividendo = 32'h%h\ndivisor   = 32'h%h\n", dividendo, divisor), 
                    $sformatf("dividendo = %d\ndivisor   = %d\n", $signed(dividendo), $signed(divisor)),
                    $sformatf("signed division")
                };
    else
        my_str = {
                    $sformatf("dividendo = 32'h%h\ndivisor   = 32'h%h\n", dividendo, divisor), 
                    $sformatf("dividendo = %0d\ndivisor   = %0d\n", $unsigned(dividendo), $unsigned(divisor)),
                    $sformatf("UNsigned division")
                };
    return my_str;
endfunction

endclass : tr_in

// Case: módulo do dividendo maior que do divisor, mesmo sinal
class div_samesig_tr extends tr_in;
    
    rand bit sign;
    rand int unsigned shamt;
    
    `uvm_object_utils_begin(div_samesig_tr)
        `uvm_field_int(shamt, UVM_ALL_ON | UVM_DEC)
    `uvm_object_utils_end

    function new(string name = "div_samesig_tr");
        super.new(name);
    endfunction

    constraint is_signed_division { 
        signal_division == 1;
    }
    constraint same_signal { 
        dividendo[31] == sign;
        divisor  [31] == sign;
    }

    constraint shamt_range { 
        shamt < 31;
        shamt > 1;
    }
    constraint greater_than { 
        solve sign, shamt before dividendo, divisor;
        if (sign == 1'b0) { // Operandos positivos
            (dividendo >> shamt) > divisor;
        } 
        else {              // Operandos negativos
            ((-dividendo) >> shamt) > (-divisor);
        }
    }

    function string convert2string();
        string my_str;
        my_str = {
            $sformatf("Signed division - same signal operands transaction\n"), 
            $sformatf("dividendo = 32'h%h\ndivisor = 32'h%h\n", dividendo, divisor), 
            $sformatf("dividendo = %0d\ndivisor = %0d\n", $signed(dividendo), $signed(divisor)),
            $sformatf("shamt = %0d", shamt)
            };
        return my_str;
    endfunction

endclass : div_samesig_tr

// Case: módulo do dividendo maior que do divisor, sinais diferentes
class div_diffsig_tr extends tr_in;
    
    rand bit sign;
    rand int unsigned shamt;
    
    `uvm_object_utils_begin(div_diffsig_tr)
        `uvm_field_int(shamt, UVM_ALL_ON | UVM_DEC)
    `uvm_object_utils_end

    function new(string name = "div_diffsig_tr");
        super.new(name);
    endfunction

    constraint is_signed_division { 
        signal_division == 1;
    }
    constraint different_signal { 
        dividendo[31] ==  sign;
        divisor  [31] == !sign;
    }

    constraint shamt_range { 
        shamt < 31;
        shamt > 1;
    }
    constraint greater_than { 
        solve sign, shamt before dividendo, divisor;
        if (sign == 1'b0) { // dividendo positivo, divisor negativo
            (dividendo >> shamt) > (-divisor);
        } 
        else {              // dividendo negativo, divisor positivo
            ((-dividendo) >> shamt) > divisor;
        }
    }

    function string convert2string();
        string my_str;
        my_str = {
            $sformatf("Signed division - different signal operands transaction\n"), 
            $sformatf("dividendo = 32'h%h\ndivisor = 32'h%h\n", dividendo, divisor), 
            $sformatf("dividendo = %0d\ndivisor = %0d\n", $signed(dividendo), $signed(divisor)),
            $sformatf("shamt = %0d", shamt)
            };
        return my_str;
    endfunction

endclass : div_diffsig_tr

//Case Dividendo baixo e divisor baixo

class item extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item)

    //Constructor
    function new(string name = "item");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo
    constraint c1 { divisor   inside {[32'h00000000:32'h000000FF]};}
    constraint c2 { dividendo inside {[32'h00000000:32'h000000FF]};}

endclass : item

//Case Dividendo alto e divisor alto

class item2 extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item2)

    //Constructor
    function new(string name = "item2");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo

    constraint c3 { divisor   inside {[32'hFFFFFF00:32'hFFFFFFFF]};}
    constraint c4 { dividendo inside {[32'hFFFFFF00:32'hFFFFFFFF]};}

endclass : item2

//Case dividendo = 0

class item3 extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item3)

    //Constructor
    function new(string name = "item3");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo
    constraint c5 { dividendo == '0;}

endclass : item3

//Case divisor = 0

class item4 extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item4)

    //Constructor
    function new(string name = "item4");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo
    constraint c8 { divisor == '0;}
endclass : item4

//Case dividendo = 1

class item5 extends tr_in;

///Utility and Field macros,
  `uvm_object_utils(item5)

  //Constructor
  function new(string name = "item5");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
  constraint c2 { dividendo == 1;}

endclass : item5

//Case divisor = 1

class item6 extends tr_in;

///Utility and Field macros,
  `uvm_object_utils(item6)

  //Constructor
  function new(string name = "item6");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo
  constraint c1 { divisor == 1;}

endclass : item6

//Case dividendo = 0 e divisor = 0

class item7 extends tr_in;

///Utility and Field macros,
  `uvm_object_utils(item7)

  //Constructor
  function new(string name = "item7");
    super.new(name);
  endfunction

  //Constraint, to generate any divisor and dividendo

  constraint c3 { divisor   == '0;}
  constraint c4 { dividendo == '0;}

endclass : item7

//Case Dividendo alto e divisor baixo

class item8 extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item8)

    //Constructor
    function new(string name = "item8");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo

    constraint c3 { divisor   inside {[32'h00000000:32'h000000FF]};}
    constraint c4 { dividendo inside {[32'hFFFFFF00:32'hFFFFFFFF]};}

endclass : item8

//Case Dividendo baixo e divisor alto

class item9 extends tr_in;

    ///Utility and Field macros,
    `uvm_object_utils(item9)

    //Constructor
    function new(string name = "item9");
        super.new(name);
    endfunction

    //Constraint, to generate any divisor and dividendo

    constraint c3 { divisor   inside {[32'hFFFFFF00:32'hFFFFFFFF]};}
    constraint c4 { dividendo inside {[32'h00000000:32'h000000FF]};}

endclass : item9
