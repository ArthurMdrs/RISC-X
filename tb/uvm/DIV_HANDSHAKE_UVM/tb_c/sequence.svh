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

class in_seq_signed extends uvm_sequence #(tr_in);
    `uvm_object_utils(in_seq_signed)
    
    function new (string name = "in_seq_signed");
      super.new(name);
    endfunction: new
    
    task body;
      tr_in tr;
      item  m_item;
      item2 m_item_2;
      item3 m_item_3;
      item4 m_item_4;
      item5 m_item_5;
      item6 m_item_6;
      item7 m_item_7;
      //item8 m_item_8;
      
      div_dist1_tr dist1_item;

      forever begin
        `uvm_do_with(tr, { signal_division == 1; })
        
        m_item   = item::type_id::create("m_item");
        m_item_2 = item2::type_id::create("m_item_2");
        m_item_3 = item3::type_id::create("m_item_3");
        m_item_4 = item4::type_id::create("m_item_4");
        m_item_5 = item5::type_id::create("m_item_5");
        m_item_6 = item6::type_id::create("m_item_6");
        m_item_7 = item7::type_id::create("m_item_7");
        //m_item_8 = item8::type_id::create("m_item_8");
        
        dist1_item = div_dist1_tr::type_id::create("dist1_item");

    	start_item(m_item);        //Start the generation of the item 
        void'(m_item.randomize() with { signal_division == 1; }); //Randomize
        finish_item(m_item);       //Finish the generation of the item

    	start_item(m_item_2);
        void'(m_item_2.randomize() with { signal_division == 1; });
        finish_item(m_item_2);

    	start_item(m_item_3);
        void'(m_item_3.randomize() with { signal_division == 1; });
        finish_item(m_item_3);

    	start_item(m_item_4);
        void'(m_item_4.randomize() with { signal_division == 1; });
        finish_item(m_item_4);

    	start_item(m_item_5);
        void'(m_item_5.randomize() with { signal_division == 1; });
        finish_item(m_item_5);

    	start_item(m_item_6);
        void'(m_item_6.randomize() with { signal_division == 1; });
        finish_item(m_item_6);

    	start_item(m_item_7);
        void'(m_item_7.randomize() with { signal_division == 1; });
        finish_item(m_item_7);

        /*
    	start_item(m_item_8);
        void'(m_item_8.randomize() with { signal_division == 1; });
        finish_item(m_item_8);
        */
        
        repeat (10) begin
            start_item(dist1_item);
            assert(dist1_item.randomize() with { signal_division == 1; });
            `uvm_info("SEQ", $sformatf("\n*************************\Sent tr:\n%s\n*************************", dist1_item.convert2string()), UVM_MEDIUM)
            finish_item(dist1_item);
        end
      end
        `uvm_info("SEQ", $sformatf("Done generation of items"), UVM_LOW)
    endtask
   
endclass

class in_seq_unsigned extends uvm_sequence #(tr_in);
    `uvm_object_utils(in_seq_unsigned)
    
    function new (string name = "in_seq_unsigned");
      super.new(name);
    endfunction: new
    
    task body;
      tr_in tr;
      item  m_item;
      item2 m_item_2;
      item3 m_item_3;
      item4 m_item_4;
      item5 m_item_5;
      item6 m_item_6;
      item7 m_item_7;
      //item8 m_item_8;
      
      div_dist1_tr dist1_item;

      forever begin
        `uvm_do_with(tr, { signal_division == 0; })
        
        m_item   = item::type_id::create("m_item");
        m_item_2 = item2::type_id::create("m_item_2");
        m_item_3 = item3::type_id::create("m_item_3");
        m_item_4 = item4::type_id::create("m_item_4");
        m_item_5 = item5::type_id::create("m_item_5");
        m_item_6 = item6::type_id::create("m_item_6");
        m_item_7 = item7::type_id::create("m_item_7");
        //m_item_8 = item8::type_id::create("m_item_8");
        
        dist1_item = div_dist1_tr::type_id::create("dist1_item");

    	start_item(m_item);        //Start the generation of the item 
        void'(m_item.randomize() with { signal_division == 0; }); //Randomize
        finish_item(m_item);       //Finish the generation of the item

    	start_item(m_item_2);
        void'(m_item_2.randomize() with { signal_division == 0; });
        finish_item(m_item_2);

    	start_item(m_item_3);
        void'(m_item_3.randomize() with { signal_division == 0; });
        finish_item(m_item_3);

    	start_item(m_item_4);
        void'(m_item_4.randomize() with { signal_division == 0; });
        finish_item(m_item_4);

    	start_item(m_item_5);
        void'(m_item_5.randomize() with { signal_division == 0; });
        finish_item(m_item_5);

    	start_item(m_item_6);
        void'(m_item_6.randomize() with { signal_division == 0; });
        finish_item(m_item_6);

    	start_item(m_item_7);
        void'(m_item_7.randomize() with { signal_division == 0; });
        finish_item(m_item_7);

        /*
    	start_item(m_item_8);
        void'(m_item_8.randomize() with { signal_division == 0; });
        finish_item(m_item_8);
        */
        
        repeat (100) begin
            `uvm_do_with(tr, { signal_division == 0; })
            start_item(dist1_item);
            assert(dist1_item.randomize() with { signal_division == 0; });
            `uvm_info("SEQ", $sformatf("\n*************************\Sent tr:\n%s\n*************************", dist1_item.convert2string()), UVM_MEDIUM)
            finish_item(dist1_item);
        end
      end
        `uvm_info("SEQ", $sformatf("Done generation of items"), UVM_LOW)
    endtask
   
endclass

class general_sequence extends uvm_sequence #(tr_in);
    `uvm_object_utils(general_sequence)
    
    function new (string name = "general_sequence");
      super.new(name);
    endfunction: new
    
    task body;
      tr_in tr;
      item  m_item;
      item2 m_item_2;
      item3 m_item_3;
      item4 m_item_4;
      item5 m_item_5;
      item6 m_item_6;
      item7 m_item_7;
      //item8 m_item_8;
      
      div_dist1_tr dist1_item;

      forever begin
        `uvm_do(tr)
        
        m_item   = item::type_id::create("m_item");
        m_item_2 = item2::type_id::create("m_item_2");
        m_item_3 = item3::type_id::create("m_item_3");
        m_item_4 = item4::type_id::create("m_item_4");
        m_item_5 = item5::type_id::create("m_item_5");
        m_item_6 = item6::type_id::create("m_item_6");
        m_item_7 = item7::type_id::create("m_item_7");
        //m_item_8 = item8::type_id::create("m_item_8");
        
        dist1_item = div_dist1_tr::type_id::create("dist1_item");

    	start_item(m_item);        //Start the generation of the item 
        void'(m_item.randomize()); //Randomize
        finish_item(m_item);       //Finish the generation of the item

    	start_item(m_item_2);
        void'(m_item_2.randomize());
        finish_item(m_item_2);

    	start_item(m_item_3);
        void'(m_item_3.randomize());
        finish_item(m_item_3);

    	start_item(m_item_4);
        void'(m_item_4.randomize());
        finish_item(m_item_4);

    	start_item(m_item_5);
        void'(m_item_5.randomize());
        finish_item(m_item_5);

    	start_item(m_item_6);
        void'(m_item_6.randomize());
        finish_item(m_item_6);

    	start_item(m_item_7);
        void'(m_item_7.randomize());
        finish_item(m_item_7);

        /*
    	start_item(m_item_8);
        void'(m_item_8.randomize());
        finish_item(m_item_8);
        */
        
        repeat (10) begin
            start_item(dist1_item);
            assert(dist1_item.randomize());
            `uvm_info("SEQ", $sformatf("\n*************************\Sent tr:\n%s\n*************************", dist1_item.convert2string()), UVM_MEDIUM)
            finish_item(dist1_item);
        end
      end
        `uvm_info("SEQ", $sformatf("Done generation of items"), UVM_LOW)
    endtask
   
endclass
