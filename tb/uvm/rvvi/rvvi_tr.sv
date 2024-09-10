// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    RVVI transaction                                           //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVVI transaction.                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class rvvi_tr #(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 32,  // GPR length in bits
    parameter int FLEN   = 32   // FPR length in bits
) extends uvm_sequence_item;
    
    rand logic [63:0]               order      ;   // Unique event order count (no gaps or reuse)

    rand logic [(ILEN-1):0]         insn       ;   // Instruction bit pattern
    rand logic                      trap       ;   // State update without instruction retirement
    rand logic                      debug_mode ;   // Retired instruction executed in debug mode

    // Program counter
    rand logic [(XLEN-1):0]         pc_rdata   ;   // PC of instruction

    // X Registers
    rand logic [31:0][(XLEN-1):0]   x_wdata    ;   // X data value
    rand logic [31:0]               x_wb       ;   // X data writeback (change) flag

    // F Registers
    rand logic [31:0][(FLEN-1):0]   f_wdata    ;   // F data value
    rand logic [31:0]               f_wb       ;   // F data writeback (change) flag

    // V Registers
    // rand logic [31:0][(VLEN-1):0]   v_wdata    ;   // V data value
    // rand logic [31:0]               v_wb       ;   // V data writeback (change) flag

    // Control and Status Registers
    rand logic [4095:0][(XLEN-1):0] csr        ;   // Full CSR Address range
    rand logic [4095:0]             csr_wb     ;   // CSR writeback (change) flag

    // Atomic Memory Control
    // rand logic                      lrsc_cancel;   // Implementation defined cancel

    // Optional
    rand logic [(XLEN-1):0]         pc_wdata   ;   // PC of next instruction
    rand logic                      intr       ;   // (RVFI Legacy) Flag first instruction of trap handler
    rand logic                      halt       ;   // Halted  instruction
    rand logic [1:0]                ixl        ;   // XLEN mode 32/64 bit
    rand logic [1:0]                mode       ;   // Privilege mode of operation

    `uvm_object_param_utils_begin(rvvi_tr#(ILEN,XLEN,FLEN))
        `uvm_field_int(order, UVM_ALL_ON)
        `uvm_field_int(insn, UVM_ALL_ON)
        `uvm_field_int(trap, UVM_ALL_ON)
        `uvm_field_int(debug_mode, UVM_ALL_ON)
        `uvm_field_int(pc_rdata, UVM_ALL_ON)
        `uvm_field_int(x_wdata, UVM_ALL_ON)
        `uvm_field_int(x_wb, UVM_ALL_ON)
        `uvm_field_int(f_wdata, UVM_ALL_ON)
        `uvm_field_int(f_wb, UVM_ALL_ON)
        // `uvm_field_int(v_wdata, UVM_ALL_ON)
        // `uvm_field_int(v_wb, UVM_ALL_ON)
        `uvm_field_int(csr, UVM_ALL_ON)
        `uvm_field_int(csr_wb, UVM_ALL_ON)
        // `uvm_field_int(lrsc_cancel, UVM_ALL_ON)
        `uvm_field_int(pc_wdata, UVM_ALL_ON)
        `uvm_field_int(intr, UVM_ALL_ON)
        `uvm_field_int(halt, UVM_ALL_ON)
        `uvm_field_int(ixl, UVM_ALL_ON)
        `uvm_field_int(mode, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name="rvvi_tr");
        super.new(name);
    endfunction: new

    // Type your constraints!
    constraint some_constraint {}

    function string convert2string();
        string string_aux;

        string_aux = {string_aux, "\n***********************************\n"};
        string_aux = {string_aux, $sformatf("** order value: %h\n", order)};
        string_aux = {string_aux, $sformatf("** insn value: %h\n", insn)};
        string_aux = {string_aux, $sformatf("** trap value: %h\n", trap)};
        string_aux = {string_aux, $sformatf("** debug_mode value: %h\n", debug_mode)};
        string_aux = {string_aux, $sformatf("** pc_rdata value: %h\n", pc_rdata)};
        // string_aux = {string_aux, $sformatf("** x_wdata value: %h\n", x_wdata)};
        // string_aux = {string_aux, $sformatf("** x_wb value: %h\n", x_wb)};
        // string_aux = {string_aux, $sformatf("** f_wdata value: %h\n", f_wdata)};
        // string_aux = {string_aux, $sformatf("** f_wb value: %h\n", f_wb)};
        // string_aux = {string_aux, $sformatf("** v_wdata value: %h\n", v_wdata)};
        // string_aux = {string_aux, $sformatf("** v_wb value: %h\n", v_wb)};
        // string_aux = {string_aux, $sformatf("** csr value: %h\n", csr)};
        // string_aux = {string_aux, $sformatf("** csr_wb value: %h\n", csr_wb)};
        // string_aux = {string_aux, $sformatf("** lrsc_cancel value: %h\n", lrsc_cancel)};
        string_aux = {string_aux, $sformatf("** pc_wdata value: %h\n", pc_wdata)};
        string_aux = {string_aux, $sformatf("** intr value: %h\n", intr)};
        string_aux = {string_aux, $sformatf("** halt value: %h\n", halt)};
        string_aux = {string_aux, $sformatf("** ixl value: %h\n", ixl)};
        string_aux = {string_aux, $sformatf("** mode value: %h\n", mode)};
        string_aux = {string_aux, "***********************************"};
        return string_aux;
    endfunction: convert2string

    // function void post_randomize();
    // endfunction: post_randomize

endclass: rvvi_tr
