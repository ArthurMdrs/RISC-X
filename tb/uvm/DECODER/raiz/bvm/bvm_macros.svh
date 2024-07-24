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

`define bvm_cover_utils(T, tr=coverage_transaction, cvrgrp=transaction_covergroup) \
  T tr;   \
  function void sample(T t); \
    tr = t; \
    cvrgrp.sample(); \
  endfunction \
  function real get_coverage(); \
    return cvrgrp.get_inst_coverage(); \
  endfunction \
  function new(string name, uvm_component parent); \
    super.new(name, parent); \
    cvrgrp = new(); \
    cvrgrp.set_inst_name({get_full_name(), ".", `"cvrgrp`"}); \
  endfunction

`define BVM_MORE_PARALLEL_STREAMS 5

`ifndef BVM_ASSERT_BEGIN_TR
  `define BVM_ASSERT_BEGIN_TR assert
`endif

`ifdef VCS
  // Overlapping transaction in time, also called pipelined transactions,
  // must be recorded in vcs as separate streams to avoid the MSGLOG-ALRDY-STRTD error.
  `define bvm_begin_tr(t) begin \
    static uvm_sequence_item stream[]; \
    int i=0; \
    string i_str, name=t.get_name(); \
    for(uvm_component c=this; c.get_parent(); c=c.get_parent()) name = {c.get_name(),"_",name}; \
    while( i<stream.size() && stream[i] != null && stream[i].is_active() ) i++; \
    if(stream.size() <= i) begin \
        uvm_sequence_item stream_copy[]; \
        stream_copy = new[stream.size()]; \
        for(int j=0; j<stream_copy.size(); j++) stream_copy[j] = stream[j]; \
        stream = new[i+`BVM_MORE_PARALLEL_STREAMS]; \
        for(int j=0; j<stream_copy.size(); j++) stream[j] = stream_copy[j]; \
    end \
    stream[i] = t; \
    i_str.itoa(i); \
    if(i) name = {name,"_",i_str}; \
    t.enable_recording(name); \
    assert(t.begin_tr()); \
    t.set_initiator(this); end
`else
  `define bvm_begin_tr(t) begin \
    t.enable_recording(t.get_full_name()); \
    `BVM_ASSERT_BEGIN_TR(begin_tr(t,t.get_full_name())); \
    t.set_initiator(this); end
`endif

`define bvm_end_tr(t)  begin \
   uvm_component c=t.get_initiator(); \
   if(c) c.end_tr(t); else end_tr(t); end

