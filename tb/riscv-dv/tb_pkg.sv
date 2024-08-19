package tb_pkg;

import core_pkg::*;

typedef struct {
    string       name;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
    logic [31:0] size;
    int          alignment;
} section_info_t;

`include "riscv_decoder.sv"
`include "mem_model.sv"

endpackage