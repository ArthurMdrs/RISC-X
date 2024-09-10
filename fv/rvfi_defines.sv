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

`define RISCV_FORMAL
`define RISCV_FORMAL_NRET 1
`define RISCV_FORMAL_XLEN 32
`define RISCV_FORMAL_ILEN 32
`define RISCV_FORMAL_CSR_MARCHID
`define RISCV_FORMAL_CSR_MCAUSE
`define RISCV_FORMAL_CSR_MEPC
`define RISCV_FORMAL_CSR_MHARTID
`define RISCV_FORMAL_CSR_MIE
`define RISCV_FORMAL_CSR_MIMPID
`define RISCV_FORMAL_CSR_MISA
`define RISCV_FORMAL_CSR_MSCRATCH
`define RISCV_FORMAL_CSR_MSTATUS
`define RISCV_FORMAL_CSR_MTVEC
`define RISCV_FORMAL_CSR_MVENDORID
`include "rvfi_macros.vh"