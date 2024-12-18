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
// Design Name:    RISC-V decoder                                             //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    A class that decodes RISC-V's binary instructions into     //
//                 mnemonics.                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

class riscv_decoder;

    // Constructor
    function new();
    endfunction

    // Function to decode an instruction and return the mnemonic
    function string decode_instruction (logic [31:0] instruction);
        logic [6:0] opcode;
        string mnemonic;
        
        // Extract the opcode
        opcode = instruction[6:0];
        
        if (instruction[1:0] == 2'b11) begin // 32-bit instructions
            // Decode based on the opcode
            case (opcode)
                OPCODE_LUI:       mnemonic = decode_lui(instruction);
                OPCODE_AUIPC:     mnemonic = decode_auipc(instruction);
                OPCODE_JAL:       mnemonic = decode_jal(instruction);
                OPCODE_JALR:      mnemonic = decode_jalr(instruction);
                OPCODE_BRANCH:    mnemonic = decode_branch(instruction);
                OPCODE_LOAD:      mnemonic = decode_load(instruction);
                OPCODE_STORE:     mnemonic = decode_store(instruction);
                OPCODE_OP_IMM:    mnemonic = decode_op_imm(instruction);
                OPCODE_OP:        mnemonic = decode_op(instruction);
                // OPCODE_MISC_MEM:  mnemonic = decode_misc_mem(instruction);
                OPCODE_SYSTEM:    mnemonic = decode_system(instruction);
                
                OPCODE_OP_FP:     mnemonic = decode_op_fp(instruction);
                OPCODE_FMADD_FP:  mnemonic = decode_fmadd(instruction);
                OPCODE_FMSUB_FP:  mnemonic = decode_fmsub(instruction);
                OPCODE_FNMADD_FP: mnemonic = decode_fnmadd(instruction);
                OPCODE_FNMSUB_FP: mnemonic = decode_fnmsub(instruction);
                OPCODE_STORE_FP : mnemonic = decode_fstore(instruction);
                OPCODE_LOAD_FP  : mnemonic = decode_fload(instruction);
                
                default:          mnemonic = "UNKNOWN";
            endcase
        end
        else begin // 16-bit instructions
            case (instruction[1:0])
                OPCODE_RVC_0: mnemonic = decode_c0(instruction[15:0]);
                OPCODE_RVC_1: mnemonic = decode_c1(instruction[15:0]);
                OPCODE_RVC_2: mnemonic = decode_c2(instruction[15:0]);
                default:      mnemonic = "UNKNOWN";
            endcase
        end
        
        return mnemonic;
    endfunction

    // Function to decode LUI instruction
    function string decode_lui(logic [31:0] instruction);
        string rd, imm;
        logic [19:0] imm_bits;
        rd = translate_register(instruction[11:7]);
        imm_bits = instruction[31:12];
        imm = $sformatf("0x%0h", imm_bits);
        return $sformatf("lui %s, %s", rd, imm);
    endfunction

    // Function to decode AUIPC instruction
    function string decode_auipc(logic [31:0] instruction);
        string rd, imm;
        logic [19:0] imm_bits;
        rd = translate_register(instruction[11:7]);
        imm_bits = instruction[31:12];
        imm = $sformatf("0x%0h", imm_bits);
        return $sformatf("auipc %s, %s", rd, imm);
    endfunction

    // Function to decode JAL instruction
    function string decode_jal(logic [31:0] instruction);
        string rd, imm;
        logic [19:0] imm_bits;
        rd = translate_register(instruction[11:7]);
        imm_bits = {instruction[31], instruction[19:12], instruction[20], instruction[30:21]};
        if (instruction[31])
            imm = $sformatf("-0x%0h", -imm_bits);
        else
            imm = $sformatf("0x%0h", imm_bits);
        return $sformatf("jal %s, %s", rd, imm);
    endfunction

    // Function to decode JALR instruction
    function string decode_jalr(logic [31:0] instruction);
        string rd, rs1, imm;
        logic [11:0] imm_bits;
        rd  = translate_register(instruction[11: 7]);
        rs1 = translate_register(instruction[19:15]);
        imm_bits = instruction[31:20];
        if (instruction[31])
            imm = $sformatf("-0x%0h", -imm_bits);
        else
            imm = $sformatf("0x%0h", imm_bits);
        return $sformatf("jalr %s, %s, %s", rd, rs1, imm);
    endfunction

    // Function to decode BRANCH instructions
    function string decode_branch(logic [31:0] instruction);
        string rs1, rs2, imm;
        string func;
        logic [12:0] imm_bits;
        rs1 = translate_register(instruction[19:15]);
        rs2 = translate_register(instruction[24:20]);
        imm_bits = {instruction[31], instruction[7], instruction[30:25], instruction[11:8], 1'b0};
        if (instruction[31])
            imm = $sformatf("-0x%0h", -imm_bits);
        else
            imm = $sformatf("0x%0h", imm_bits);
        case (instruction[14:12])
            3'b000: func = "beq";
            3'b001: func = "bne";
            3'b100: func = "blt";
            3'b101: func = "bge";
            3'b110: func = "bltu";
            3'b111: func = "bgeu";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s, %s", func, rs1, rs2, imm);
    endfunction

    // Function to decode LOAD instructions
    function string decode_load(logic [31:0] instruction);
        string rd, rs1, imm;
        string func;
        logic [11:0] imm_bits;
        rd  = translate_register(instruction[11:7]);
        rs1 = translate_register(instruction[19:15]);
        imm_bits = instruction[31:20];
        imm = $sformatf("0x%0h", imm_bits);
        case (instruction[14:12])
            3'b000: func = "lb";
            3'b001: func = "lh";
            3'b010: func = "lw";
            3'b100: func = "lbu";
            3'b101: func = "lhu";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s(%s)", func, rd, imm, rs1);
    endfunction

    // Function to decode STORE instructions
    function string decode_store(logic [31:0] instruction);
        string rs1, rs2, imm;
        string func;
        logic [11:0] imm_bits;
        rs1 = translate_register(instruction[19:15]);
        rs2 = translate_register(instruction[24:20]);
        imm_bits = {instruction[31:25], instruction[11:7]};
        imm = $sformatf("0x%0h", imm_bits);
        case (instruction[14:12])
            3'b000: func = "sb";
            3'b001: func = "sh";
            3'b010: func = "sw";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s(%s)", func, rs2, imm, rs1);
    endfunction

    // Function to decode OP-IMM instructions
    function string decode_op_imm(logic [31:0] instruction);
        string rd, rs1, imm;
        string func;
        logic [11:0] imm_bits;
        rd  = translate_register(instruction[11:7]);
        rs1 = translate_register(instruction[19:15]);
        imm_bits = instruction[31:20];
        if (instruction[31])
            imm = $sformatf("-%0d", -imm_bits);
        else
            imm = $sformatf("%0d", imm_bits);
        case (instruction[14:12])
            3'b000: func = "addi";
            3'b001: func = (instruction[31:25]==7'h0) ? ("slli") : ("UNKNOWN");
            3'b010: func = "slti";
            3'b011: func = "sltiu";
            3'b100: func = "xori";
            3'b101: func = (instruction[31:25]==7'h0) ? ("srli") : ((instruction[31:25]==7'h20) ? ("srai") : ("UNKNOWN"));
            3'b110: func = "ori";
            3'b111: func = "andi";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s, %s", func, rd, rs1, imm);
    endfunction

    // Function to decode OP instructions
    function string decode_op(logic [31:0] instruction);
        string rd, rs1, rs2;
        string func;
        
        rd  = translate_register(instruction[11:7]);
        rs1 = translate_register(instruction[19:15]);
        rs2 = translate_register(instruction[24:20]);
        if (instruction[31:25] == 7'b0000001) begin
            case (instruction[14:12])
                3'b000: func = "mul";
                3'b001: func = "mulh";
                3'b010: func = "mulhsu";
                3'b011: func = "mulhu";
                3'b100: func = "div";
                3'b101: func = "divu";
                3'b110: func = "rem";
                3'b111: func = "remu";
                default: func = "UNKNOWN";
            endcase
        end else begin
            case (instruction[14:12])
                3'b000: func = (instruction[30] == 1'b0) ? "add" : "sub";
                3'b001: func = "sll";
                3'b010: func = "slt";
                3'b011: func = "sltu";
                3'b100: func = "xor";
                3'b101: func = (instruction[30] == 1'b0) ? "srl" : "sra";
                3'b110: func = "or";
                3'b111: func = "and";
                default: func = "UNKNOWN";
            endcase
        end
        
        
        

        

        return $sformatf("%s %s, %s, %s", func, rd, rs1, rs2);
        // return $sformatf("%s x%0d, x%0d, x%0d", func, instruction[11:7], instruction[19:15], instruction[24:20]);
    endfunction

    // Function to decode MISC-MEM instructions
    function string decode_misc_mem(logic [31:0] instruction);
        return $sformatf("fence");
    endfunction

    // Function to decode SYSTEM instructions
    function string decode_system(logic [31:0] instruction);
        string rd, rs1;
        string csr_name;
        csr_addr_t csr_addr;
        rd  = translate_register(instruction[11:7]);
        rs1 = translate_register(instruction[19:15]);
        if (instruction[14:12] == '0) begin
            if ({instruction[19:15], instruction[11:7]} == '0) begin
                case (instruction[31:20])
                    12'h000: begin // ecall
                        return $sformatf("ecall");
                    end
                    12'h001: begin // ebreak
                        return $sformatf("ebreak");
                    end
                    12'h302: begin // mret
                        return $sformatf("mret");
                    end
                    12'h002: begin // uret
                        return $sformatf("uret");
                    end
                    12'h7b2: begin // dret
                        return $sformatf("dret");
                    end
                    12'h105: begin // wfi
                        return $sformatf("wfi");
                    end
                    default: begin
                        return $sformatf("UNKNOWN");
                    end
                endcase
            end
            else begin
                return $sformatf("UNKNOWN");
            end
        end
        else begin
            csr_addr = csr_addr_t'(instruction[31:20]);
            csr_name = translate_csr(csr_addr);
            
            case (instruction[14:12])
                3'b001: begin // csrrw
                    return $sformatf("csrrw %s, %s, %s", rd, csr_name, rs1); 
                end
                3'b010: begin // csrrs
                    return $sformatf("csrrs %s, %s, %s", rd, csr_name, rs1); 
                end
                3'b011: begin // csrrc
                    return $sformatf("csrrc %s, %s, %s", rd, csr_name, rs1); 
                end
                3'b101: begin // csrrwi
                    return $sformatf("csrrwi %s, %s, 0x%0h", rd, csr_name, instruction[19:15]); 
                end
                3'b110: begin // csrrsi
                    return $sformatf("csrrsi %s, %s, 0x%0h", rd, csr_name, instruction[19:15]); 
                end
                3'b111: begin // csrrci
                    return $sformatf("csrrci %s, %s, 0x%0h", rd, csr_name, instruction[19:15]); 
                end
                default: begin
                    return $sformatf("UNKNOWN"); 
                end
            endcase
        end
    endfunction

    // Function to translate register number to mnemonic
    function string translate_register(logic [4:0] reg_num, logic is_f = 0);
        if (!is_f) begin // Integer x registers
            case (reg_num)
                5'd0:  return "zero";
                5'd1:  return "ra";
                5'd2:  return "sp";
                5'd3:  return "gp";
                5'd4:  return "tp";
                5'd5:  return "t0";
                5'd6:  return "t1";
                5'd7:  return "t2";
                5'd8:  return "s0";
                5'd9:  return "s1";
                5'd10: return "a0";
                5'd11: return "a1";
                5'd12: return "a2";
                5'd13: return "a3";
                5'd14: return "a4";
                5'd15: return "a5";
                5'd16: return "a6";
                5'd17: return "a7";
                5'd18: return "s2";
                5'd19: return "s3";
                5'd20: return "s4";
                5'd21: return "s5";
                5'd22: return "s6";
                5'd23: return "s7";
                5'd24: return "s8";
                5'd25: return "s9";
                5'd26: return "s10";
                5'd27: return "s11";
                5'd28: return "t3";
                5'd29: return "t4";
                5'd30: return "t5";
                5'd31: return "t6";
                default: return "UNKNOWN_REG";
            endcase
        end
        else begin // Floating point f registers
            case (reg_num)
                5'd0:  return "ft0";
                5'd1:  return "ft1";
                5'd2:  return "ft2";
                5'd3:  return "ft3";
                5'd4:  return "ft4";
                5'd5:  return "ft5";
                5'd6:  return "ft6";
                5'd7:  return "ft7";
                5'd8:  return "fs0";
                5'd9:  return "fs1";
                5'd10: return "fa0";
                5'd11: return "fa1";
                5'd12: return "fa2";
                5'd13: return "fa3";
                5'd14: return "fa4";
                5'd15: return "fa5";
                5'd16: return "fa6";
                5'd17: return "fa7";
                5'd18: return "fs2";
                5'd19: return "fs3";
                5'd20: return "fs4";
                5'd21: return "fs5";
                5'd22: return "fs6";
                5'd23: return "fs7";
                5'd24: return "fs8";
                5'd25: return "fs9";
                5'd26: return "fs10";
                5'd27: return "fs11";
                5'd28: return "ft8";
                5'd29: return "ft9";
                5'd30: return "ft10";
                5'd31: return "ft11";
                default: return "UNKNOWN_REG";
            endcase
        end
    endfunction

    // Function to translate CSR address to mnemonic
    function string translate_csr(csr_addr_t csr_addr);
        string str;
        str = csr_addr.name(); // CSR name is defined in the typedef as CSR_NAME
        str = str.tolower();   // Make everything lowercase
        str = str.substr(4,str.len()-1); // Drop the "csr_" part
        return str;
    endfunction
    
    // Function to decode compressed first quadrant instructions
    function string decode_c0(logic [15:0] instr);
        string rd, rs1, rs2, imm;
        logic [9:0] imm_bits;
        rs1 = translate_register({2'b01, instr[9:7]});
        case (instr[15:13])
            3'b000: begin
                if (instr[12:5] == '0)
                    return "UNKNOWN";
                rd  = translate_register({2'b01, instr[4:2]});
                rs1 = "sp";
                imm_bits = {instr[10:7], instr[12:11], instr[5], instr[6], 2'b0};
                imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.addi4spn %s, %s, %s", rd, rs1, imm);
            end
            3'b010: begin
                rd  = translate_register({2'b01, instr[4:2]});
                imm_bits = {instr[5], instr[12:10], instr[6], 2'b0};
                imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.lw %s, %s(%s)", rd, imm, rs1);
            end
            3'b011: begin
                rd  = translate_register({2'b01, instr[4:2]}, 1);
                imm_bits = {instr[5], instr[12:10], instr[6], 2'b0};
                imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.flw %s, %s(%s)", rd, imm, rs1);
            end
            3'b110: begin
                rs2 = translate_register({2'b01, instr[4:2]});
                imm_bits = {instr[5], instr[12:10], instr[6], 2'b0};
                imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.sw %s, %s(%s)", rs2, imm, rs1);
            end
            3'b111: begin
                rs2 = translate_register({2'b01, instr[4:2]}, 1);
                imm_bits = {instr[5], instr[12:10], instr[6], 2'b0};
                imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.fsw %s, %s(%s)", rs2, imm, rs1);
            end
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Function to decode compressed second quadrant instructions
    function string decode_c1(logic [15:0] instr);
        string rd, rs1, rs2, imm;
        logic [11:0] imm_bits;
        case (instr[15:13])
            3'b000: begin
                if (instr[4:2] == '0)
                    return "c.nop";
                rd  = translate_register(instr[11:7]);
                imm_bits = {instr[12], instr[6:2]};
                if (instr[12]) imm = $sformatf("-%0d", -imm_bits);
                else           imm = $sformatf("%0d", imm_bits);
                return $sformatf("c.addi %s, %s", rd, imm);
            end
            3'b001: begin
                rd  = "ra";
                imm_bits = {instr[12], instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], 1'b0};
                if (instr[12]) imm = $sformatf("-0x%0h", -imm_bits);
                else           imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.jal %s, %s", rd, imm);
            end
            3'b010: begin
                rd  = translate_register(instr[11:7]);
                imm_bits = {instr[12], instr[6:2]};
                if (instr[12]) imm = $sformatf("-%0d", -imm_bits);
                else           imm = $sformatf("%0d", imm_bits);
                return $sformatf("c.li %s, %s", rd, imm);
            end
            3'b011: begin
                if ({instr[12], instr[6:2]} == '0)
                    return "UNKNOWN";
                rd  = translate_register(instr[11:7]);
                if(rd == "sp") begin
                    imm_bits = {instr[12], instr[4:3], instr[5], instr[2], instr[6], 4'b0};
                    if (instr[12]) imm = $sformatf("-%0d", -imm_bits);
                    else           imm = $sformatf("%0d", imm_bits);
                    return $sformatf("c.addi16sp %s, %s", rd, imm);
                end
                else begin
                    imm_bits = {instr[12], instr[6:2]};
                    imm = $sformatf("0x%0h", imm_bits);
                    return $sformatf("c.lui %s, %s", rd, imm);
                end
            end
            3'b100: begin
                case (instr[11:10])
                    2'b00: begin
                        if (instr[12] == 1'b1)
                            return "UNKNOWN";
                        rd  = translate_register({2'b01, instr[9:7]});
                        imm_bits = {instr[12], instr[6:2]};
                        imm = $sformatf("%0d", imm_bits);
                        return $sformatf("c.srli %s, %s", rd, imm);
                    end
                    2'b01: begin
                        if (instr[12] == 1'b1)
                            return "UNKNOWN";
                        rd  = translate_register({2'b01, instr[9:7]});
                        imm_bits = {instr[12], instr[6:2]};
                        imm = $sformatf("%0d", imm_bits);
                        return $sformatf("c.srai %s, %s", rd, imm);
                    end
                    2'b10: begin
                        rd  = translate_register({2'b01, instr[9:7]});
                        imm_bits = {instr[12], instr[6:2]};
                        if (instr[12]) imm = $sformatf("-%0d", -imm_bits);
                        else           imm = $sformatf("%0d", imm_bits);
                        return $sformatf("c.andi %s, %s", rd, imm);
                    end
                    2'b11: begin
                        rd  = translate_register({2'b01, instr[9:7]});
                        rs2 = translate_register({2'b01, instr[4:2]});
                        case (instr[6:5])
                            2'b00: return $sformatf("c.sub %s, %s", rd, rs2);
                            2'b01: return $sformatf("c.xor %s, %s", rd, rs2);
                            2'b10: return $sformatf("c.or %s, %s", rd, rs2);
                            2'b11: return $sformatf("c.and %s, %s", rd, rs2);
                            default: return "UNKNOWN";
                        endcase
                    end
                    default: return "UNKNOWN";
                endcase
            end
            3'b101: begin
                imm_bits = {instr[12], instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], 1'b0};
                if (instr[12]) imm = $sformatf("-0x%0h", -imm_bits);
                else           imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.j %s", imm);
            end
            3'b110: begin
                rs1 = translate_register({2'b01, instr[9:7]});
                imm_bits = {instr[12], instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0};
                if (instr[12]) imm = $sformatf("-0x%0h", -imm_bits);
                else           imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.beqz %s, %s", rs1, imm);
            end
            3'b111: begin
                rs1 = translate_register({2'b01, instr[9:7]});
                imm_bits = {instr[12], instr[6:5], instr[2], instr[11:10], instr[4:3], 1'b0};
                if (instr[12]) imm = $sformatf("-0x%0h", -imm_bits);
                else           imm = $sformatf("0x%0h", imm_bits);
                return $sformatf("c.bnez %s, %s", rs1, imm);
            end
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Function to decode third quadrant compressed instructions
    function string decode_c2(logic [15:0] instr);
        string rd, rs1, rs2, imm;
        logic [7:0] imm_bits;
        case (instr[15:13])
            3'b000: begin
                if (instr[12] == 1'b1)
                    return "UNKNOWN";
                rd  = translate_register(instr[11:7]);
                imm_bits = {instr[12], instr[6:2]};
                imm = $sformatf("%0d", imm_bits);
                return $sformatf("c.slli %s, %s", rd, imm);
            end
            3'b010: begin
                if (instr[11:7] == '0)
                    return "UNKNOWN";
                rd  = translate_register(instr[11:7]);
                imm_bits = {instr[3:2], instr[12], instr[6:4], 2'b0};
                imm = $sformatf("0x%0d", imm_bits); 
                return $sformatf("c.lwsp %s, %s(sp)", rd, imm);
            end
            3'b011: begin
                rd  = translate_register(instr[11:7], 1);
                imm_bits = {instr[3:2], instr[12], instr[6:4], 2'b0};
                imm = $sformatf("0x%0d", imm_bits); 
                return $sformatf("c.flwsp %s, %s(sp)", rd, imm);
            end
            3'b100: begin
                rd  = translate_register(instr[11:7]);
                rs1 = rd;
                rs2 = translate_register(instr[ 6:2]);
                if (instr[12] == 1'b0) begin
                    if(instr[6:2] == '0) begin
                        if(instr[11:7] == '0)
                            return "UNKNOWN";
                        return $sformatf("c.jr %s", rs1);
                    end
                    else begin
                        return $sformatf("c.mv %s, %s", rd, rs2);
                    end
                end
                else begin
                    if(instr[6:2] == '0) begin
                        if(instr[11:7] == '0)
                            return "c.ebreak";
                        return $sformatf("c.jalr %s", rs1);
                    end
                    else begin
                        return $sformatf("c.add %s, %s", rd, rs2);
                    end
                end
            end
            3'b110: begin
                rs2 = translate_register(instr[6:2]);
                imm_bits = {instr[8:7], instr[12:9], 2'b0};
                imm = $sformatf("0x%0d", imm_bits); 
                return $sformatf("c.swsp %s, %s(sp)", rs2, imm);
            end
            3'b111: begin
                rs2 = translate_register(instr[6:2], 1);
                imm_bits = {instr[8:7], instr[12:9], 2'b0};
                imm = $sformatf("0x%0d", imm_bits); 
                return $sformatf("c.fswsp %s, %s(sp)", rs2, imm);
            end
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Function to decode FP OP instructions
    function string decode_op_fp(logic [31:0] instruction);
        string rd, rs1, rs2;
        string func;
        bit use_2_ops;
        use_2_ops = 1;
        rd  = translate_register(instruction[11:7] , 1);
        rs1 = translate_register(instruction[19:15], 1);
        rs2 = translate_register(instruction[24:20], 1);
        case (instruction[31:25])
            7'b000_0000: begin
                func = "fadd.s";
            end
            7'b000_0100: begin
                func = "fsub.s";
            end
            7'b000_1000: begin
                func = "fmul.s";
            end
            7'b000_1100: begin
                func = "fdiv.s";
            end
            7'b010_1100: begin
                if (instruction[24:20] != 5'b0)
                    return "UNKNOWN";
                func = "fsqrt.s";
                use_2_ops = 0;
            end
            7'b001_0000: begin
                case (instruction[14:12])
                    3'b000: func = "fsgnj.s";
                    3'b001: func = "fsgnjn.s";
                    3'b010: func = "fsgnjx.s";
                    default: return "UNKNOWN";
                endcase
            end
            7'b001_0100: begin
                case (instruction[14:12])
                    3'b000: func = "fmin.s";
                    3'b001: func = "fmax.s";
                    default: return "UNKNOWN";
                endcase
            end
            7'b110_0000: begin
                case (instruction[24:20])
                    5'b00000: func = "fcvt.w.s";
                    5'b00001: func = "fcvt.wu.s";
                    default: return "UNKNOWN";
                endcase
                rd  = translate_register(instruction[11:7] , 0);
                use_2_ops = 0;
            end
            7'b110_1000: begin
                case (instruction[24:20])
                    5'b00000: func = "fcvt.s.w";
                    5'b00001: func = "fcvt.s.wu";
                    default: return "UNKNOWN";
                endcase
                rs1 = translate_register(instruction[19:15], 0);
                use_2_ops = 0;
            end
            7'b101_0000: begin
                case (instruction[14:12])
                    3'b000: func = "fle.s";
                    3'b001: func = "flt.s";
                    3'b010: func = "feq.s";
                    default: return "UNKNOWN";
                endcase
                rd  = translate_register(instruction[11:7] , 0);
            end
            7'b111_0000: begin
                if (instruction[24:20] != 5'b0)
                    return "UNKNOWN";
                case (instruction[14:12])
                    3'b000: func = "fmv.x.w";
                    3'b001: func = "fclass.s";
                    default: return "UNKNOWN";
                endcase
                rd  = translate_register(instruction[11:7] , 0);
                use_2_ops = 0;
            end
            7'b111_1000: begin
                if (instruction[24:20] != 5'b0)
                    return "UNKNOWN";
                if (instruction[14:12] != 3'b0)
                    return "UNKNOWN";
                rs1 = translate_register(instruction[19:15], 0);
                use_2_ops = 0;
                func = "fmv.w.x";
            end
            default: func = "UNKNOWN";
        endcase
        if (use_2_ops) return $sformatf("%s %s, %s, %s", func, rd, rs1, rs2);
        else           return $sformatf("%s %s, %s", func, rd, rs1);
    endfunction
    
    // Function to decode FMADD instructions
    function string decode_fmadd(logic [31:0] instruction);
        string rd, rs1, rs2, rs3;
        if (instruction[26:25] != 2'b0)
            return "UNKNOWN";
        rd  = translate_register(instruction[11:7] , 1);
        rs1 = translate_register(instruction[19:15], 1);
        rs2 = translate_register(instruction[24:20], 1);
        rs3 = translate_register(instruction[31:27], 1);
        return $sformatf("fmadd.s %s, %s, %s, %s", rd, rs1, rs2, rs3);
    endfunction
    
    // Function to decode FMSUB instructions
    function string decode_fmsub(logic [31:0] instruction);
        string rd, rs1, rs2, rs3;
        if (instruction[26:25] != 2'b0)
            return "UNKNOWN";
        rd  = translate_register(instruction[11:7] , 1);
        rs1 = translate_register(instruction[19:15], 1);
        rs2 = translate_register(instruction[24:20], 1);
        rs3 = translate_register(instruction[31:27], 1);
        return $sformatf("fmsub.s %s, %s, %s, %s", rd, rs1, rs2, rs3);
    endfunction
    
    // Function to decode FMNADD instructions
    function string decode_fnmadd(logic [31:0] instruction);
        string rd, rs1, rs2, rs3;
        if (instruction[26:25] != 2'b0)
            return "UNKNOWN";
        rd  = translate_register(instruction[11:7] , 1);
        rs1 = translate_register(instruction[19:15], 1);
        rs2 = translate_register(instruction[24:20], 1);
        rs3 = translate_register(instruction[31:27], 1);
        return $sformatf("fnmadd.s %s, %s, %s, %s", rd, rs1, rs2, rs3);
    endfunction
    
    // Function to decode FNMSUB instructions
    function string decode_fnmsub(logic [31:0] instruction);
        string rd, rs1, rs2, rs3;
        if (instruction[26:25] != 2'b0)
            return "UNKNOWN";
        rd  = translate_register(instruction[11:7] , 1);
        rs1 = translate_register(instruction[19:15], 1);
        rs2 = translate_register(instruction[24:20], 1);
        rs3 = translate_register(instruction[31:27], 1);
        return $sformatf("fnmsub.s %s, %s, %s, %s", rd, rs1, rs2, rs3);
    endfunction

    // Function to decode FP STORE instructions
    function string decode_fstore(logic [31:0] instruction);
        string rs1, rs2, imm;
        string func;
        logic [11:0] imm_bits;
        rs1 = translate_register(instruction[19:15]);
        rs2 = translate_register(instruction[24:20], 1);
        imm_bits = {instruction[31:25], instruction[11:7]};
        imm = $sformatf("0x%0h", imm_bits);
        case (instruction[14:12])
            3'b010: func = "fsw";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s(%s)", func, rs2, imm, rs1);
    endfunction

    // Function to decode FP LOAD instructions
    function string decode_fload(logic [31:0] instruction);
        string rd, rs1, imm;
        string func;
        logic [11:0] imm_bits;
        rd  = translate_register(instruction[11:7], 1);
        rs1 = translate_register(instruction[19:15]);
        imm_bits = instruction[31:20];
        imm = $sformatf("0x%0h", imm_bits);
        case (instruction[14:12])
            3'b010: func = "flw";
            default: func = "UNKNOWN";
        endcase
        return $sformatf("%s %s, %s(%s)", func, rd, imm, rs1);
    endfunction
    
endclass