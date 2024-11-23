//----------------------------------------------------------------------
//  Copyright (c) 2017 by UFCG
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//----------------------------------------------------------------------

// Author: Elmar Melcher, UFCG
// Date:   22-Jun-2017

class bvm_comparator #( type T = int ) extends uvm_scoreboard;

  typedef bvm_comparator #(T) this_type;
  `uvm_component_param_utils(this_type)

  uvm_put_imp #(T, this_type) from_refmod;
  uvm_analysis_imp #(T, this_type) from_dut;

  protected uvm_tlm_analysis_fifo #(T) fifo_dut;

  protected int m_matches, m_mismatches;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    from_refmod = new("from_refmod", this);
    from_dut = new("from_dut", this);
    fifo_dut = new("fifo_dut", this);
    m_matches = 0;
    m_mismatches = 0;
  endfunction

  function string get_type_name();
    T t = new();
    return $sformatf("bvm_comparator #(%s)", t.get_type_name());
  endfunction

  protected function void match(T exp, rec);
     if(exp.compare(rec)) begin
       `uvm_info("Match", {"\n", exp.sprint()}, UVM_HIGH);
       m_matches++;
     end
     else begin
       `uvm_warning("Mismatch", {"received\n", rec.sprint(),
                                 "differs from expected\n", exp.sprint()});
       m_mismatches++;
     end
     `bvm_end_tr(exp);
     `bvm_end_tr(rec);
  endfunction

  task put(T exp);
     T rec;
     fifo_dut.get(rec);
     match(exp, rec);
  endtask

  function bit try_put(T exp);
    T rec;
    if(fifo_dut.try_get(rec)) begin
      match(exp, rec);
      return 1;
    end
    else return 0;
  endfunction

  function bit can_put();
    return(fifo_dut.can_get());
  endfunction

  function void write(T t);
     fifo_dut.write(t);
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(),
              $sformatf("%d matches, %d mismatches", m_matches, m_mismatches),
              UVM_NONE)
  endfunction

endclass
