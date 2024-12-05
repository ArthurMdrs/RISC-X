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

// function call that provides simulation time clock
import "DPI-C" pure function int system_clock();
// coverage is checked at each increase of system_clock()

class bvm_cover #( type T = int ) extends uvm_subscriber #(T);
  protected uvm_phase running_phase; // variable to save run_phase
  protected real last_coverage =-1;  // coverage value when last checked
  protected longint last_clock = 0;  // system_clock value at last transaction received

  typedef bvm_cover #(T) this_type;
  `uvm_component_param_utils(this_type)

  const static string type_name = "bvm_cover #(T)";
  function string get_type_name();
    return type_name;
  endfunction

  function new(string name, uvm_component parent);
    super.new(name, parent);
    last_clock=system_clock();
  endfunction

  task run_phase(uvm_phase phase);
    running_phase = phase;  // save phase so it can be used by function write()
    running_phase.raise_objection(this);
  endtask: run_phase

  function void write(T t);
    real coverage;
    int clock;

    sample(t); // sample coverage with this transaction
    clock = system_clock();
    if(clock>last_clock) begin // if system_clock has advanced
      last_clock=clock;
      coverage=get_coverage();
      `uvm_info(get_type_name(),
                $sformatf("Coverage: %2.0f%% %s",
                          coverage,
                          coverage>last_coverage ? "" : "steady"),
                UVM_LOW)
      last_coverage = coverage;
      if(coverage>99 && running_phase!=null) begin
        running_phase.drop_objection(this);
        running_phase = null;
     end
    end
  endfunction

  virtual function void sample(T t);
     `uvm_fatal("BVM_COVER", "Use macro `bvm_cover_utils()")
  endfunction

  virtual function real get_coverage();
    `uvm_fatal("BVM_COVER", "Use macro `bvm_cover_utils()")
    return 0.0;
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(),
              $sformatf("Coverage: %2.0f%%",get_coverage()),
              UVM_NONE)
  endfunction

endclass

