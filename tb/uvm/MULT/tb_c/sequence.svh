// ----------------------------------------------------------------------------------------------------
// DESCRIÇÃO: Classe `sequencer` para verificação UVM do multiplicador binário de 32x32 bits
//             - Gera sequência de transações para estimular o DUT.
//             - Configura cenários de teste, como valores limites e casos de corner.
// ----------------------------------------------------------------------------------------------------
// RELEASE HISTORY  :
// DATA                 VERSÃO      AUTOR                    DESCRIÇÃO
// 2024-09-20           0.1         Cleisson                 Versão inicial.
//                                  Pedro Henrique
//                                  
// ----------------------------------------------------------------------------------------------------

class out_sequence extends uvm_sequence #(tr_out);
    `uvm_object_utils(out_sequence)
    
    function new (string name = "out_sequence");
      super.new(name);
    endfunction: new

    task body;
      tr_out tr;
      forever begin
        `uvm_do(tr)
      end
    endtask
   
endclass : out_sequence

class in_sequence extends uvm_sequence #(tr_in);
    `uvm_object_utils(in_sequence)
    //Constructor
    function new (string name = "in_sequence");
      super.new(name);
    endfunction: new
    
    task body;
      tr_in tr;
      item m_item;
      item2 m_item_2;
      item3 m_item_3;
      item4 m_item_4;
      item5 m_item_5;
      item6 m_item_6;
      item7 m_item_7;
      
      forever begin
       `uvm_do(tr)
        m_item = item::type_id::create("m_item");
        m_item_2 = item2::type_id::create("m_item_2");
        m_item_3 = item3::type_id::create("m_item_3");
        m_item_4 = item4::type_id::create("m_item_4");
        m_item_5 = item5::type_id::create("m_item_5");
        m_item_6 = item6::type_id::create("m_item_6");
        m_item_7 = item7::type_id::create("m_item_7");

      //Start the generation of the item 
    	  start_item(m_item);
      //Randomize
        void'(m_item.randomize());
      //Finish the generation of the item
        finish_item(m_item);

      //Start the generation of the item2 
    	  start_item(m_item_2);
      //Randomize
        void'(m_item_2.randomize());
      //Finish the generation of the item
        finish_item(m_item_2);

      //Start the generation of the item2 
    	  start_item(m_item_3);
      //Randomize
        void'(m_item_3.randomize());
      //Finish the generation of the item
        finish_item(m_item_3);

      //Start the generation of the item2 
    	  start_item(m_item_4);
      //Randomize
        void'(m_item_4.randomize());
      //Finish the generation of the item
        finish_item(m_item_4);

      //Start the generation of the item2 
    	  start_item(m_item_5);
      //Randomize
        void'(m_item_5.randomize());
      //Finish the generation of the item
        finish_item(m_item_5);

      //Start the generation of the item2 
    	  start_item(m_item_6);
      //Randomize
        void'(m_item_6.randomize());
      //Finish the generation of the item
        finish_item(m_item_6);

      //Start the generation of the item2 
    	  start_item(m_item_7);
      //Randomize
        void'(m_item_7.randomize());
      //Finish the generation of the item
        finish_item(m_item_7);

      end
        `uvm_info("SEQ", $sformatf("Done generation of items"), UVM_LOW)
    endtask
   
endclass : in_sequence
