module decoder import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    // ALU related signals
	output alu_operation_t    alu_operation_o,
    output alu_source_1_t     alu_source_1_o, 
    output alu_source_2_t     alu_source_2_o, 
    output immediate_source_t immediate_type_o,
    // output logic              alu_en_o, // Disable ALU to save some power?
    
    // Source/destiny general purpose registers
    output logic [4:0] rs1_addr_o,
    output logic [4:0] rs2_addr_o,
    output logic [4:0] rd_addr_o,
    
    // Memory access related signals
    output logic       mem_wen_o,
    output data_type_t mem_data_type_o,
    output logic       mem_sign_extend_o,
    
    // Write enable for ALU and mem access operations
    output logic       reg_alu_wen_o, 
    output logic       reg_mem_wen_o, 
    
    // Control transfer related signals
    output pc_source_t   pc_source_o, 
    output logic         is_branch_o,
    
    // CSR related signals
    output logic           csr_access_o,
    output csr_operation_t csr_op_o,
    
    // Indicate MRET
    output logic is_mret_o,
    
    // Decoded an illegal instruction
    output logic illegal_instr_o,
    
    // Instruction to be decoded
	input  logic [31:0] instr_i
);

logic [6:0] funct7;
logic [2:0] funct3;
logic [6:0] opcode;

assign funct7 = instr_i[31:25];
assign funct3 = instr_i[14:12];
assign opcode = instr_i[ 6: 0];

assign rs1_addr_o = instr_i[19:15];
assign rs2_addr_o = instr_i[24:20];
assign rd_addr_o  = instr_i[11: 7];

always_comb begin
    alu_operation_o  = ALU_ADD;
    alu_source_1_o   = ALU_SCR1_RS1;
    alu_source_2_o   = ALU_SCR2_RS2;
    immediate_type_o = IMM_I;
    
    mem_wen_o         = 1'b0;
    mem_data_type_o   = WORD;
    mem_sign_extend_o = 1'b0;
    
    reg_alu_wen_o = 1'b0;
    reg_mem_wen_o = 1'b0;
    
    pc_source_o = PC_NEXT;
    is_branch_o = 1'b0;
    
    csr_access_o = 1'b0;
    csr_op_o     = CSR_READ;
    
    is_mret_o = 1'b0;
    
    illegal_instr_o = 1'b0;
    
    unique case (opcode)
        /////////////////////////////////////////////
        /////////////        ALU        /////////////
        /////////////////////////////////////////////
        OPCODE_OP: begin
            // if ({instr_i[31], instr_i[29:25]} != 6'b0) // funct7 must be 7'h00 or 7'h20
            if (!(funct7 inside {7'h00, 7'h20}))
                illegal_instr_o = 1'b1;
            
            reg_alu_wen_o = 1'b1;
            
            if (funct7[5] == 1'b0) begin // funct7 == 7'h00
                unique case(funct3)
                    3'b000: alu_operation_o = ALU_ADD;  // add
                    3'b100: alu_operation_o = ALU_XOR;  // xor
                    3'b110: alu_operation_o = ALU_OR ;  // or
                    3'b111: alu_operation_o = ALU_AND;  // and
                    3'b001: alu_operation_o = ALU_SLL;  // sll
                    3'b101: alu_operation_o = ALU_SRL;  // srl
                    3'b010: alu_operation_o = ALU_SLT;  // slt
                    3'b011: alu_operation_o = ALU_SLTU; // sltu
                    default: illegal_instr_o = 1'b1;
                endcase
            end
            else begin  // funct7 == 7'h20
                unique case(funct3)
                    3'b000: alu_operation_o = ALU_SUB; // sub
                    3'b101: alu_operation_o = ALU_SRA; // sra
                    default: illegal_instr_o = 1'b1;
                endcase
            end
        end
        
        OPCODE_OP_IMM: begin
            alu_source_2_o = ALU_SCR2_IMM;
            reg_alu_wen_o  = 1'b1;
            
            unique case(funct3)
                3'b000: alu_operation_o = ALU_ADD;  // addi
                3'b100: alu_operation_o = ALU_XOR;  // xori
                3'b110: alu_operation_o = ALU_OR ;  // ori
                3'b111: alu_operation_o = ALU_AND;  // andi
                3'b001: begin                       // slli
                    alu_operation_o = ALU_SLL;
                    if (instr_i[31:25] != 7'h00)
                        illegal_instr_o = 1'b1;
                end
                3'b101: begin
                    if (instr_i[31:25] == 7'h00)
                        alu_operation_o = ALU_SRL;  // srli
                    else if (instr_i[31:25] == 7'h20)
                        alu_operation_o = ALU_SRA;  // srai
                    else 
                        illegal_instr_o = 1'b1;
                end
                3'b010: alu_operation_o = ALU_SLT;  // slti
                3'b011: alu_operation_o = ALU_SLTU; // sltiu
                default: illegal_instr_o = 1'b1;
            endcase
        end
        
        OPCODE_LUI: begin // lui
            alu_operation_o  = ALU_ADD;
            alu_source_1_o   = ALU_SCR1_ZERO;
            alu_source_2_o   = ALU_SCR2_IMM;
            immediate_type_o = IMM_U;
            
            reg_alu_wen_o  = 1'b1;
        end
        
        OPCODE_AUIPC: begin // auipc
            alu_operation_o  = ALU_ADD;
            alu_source_1_o   = ALU_SCR1_PC;
            alu_source_2_o   = ALU_SCR2_IMM;
            immediate_type_o = IMM_U;
            
            reg_alu_wen_o  = 1'b1;
        end
        
        /////////////////////////////////////////////
        ///////////    Loads / Stores    ////////////
        /////////////////////////////////////////////
        OPCODE_LOAD: begin
            alu_operation_o  = ALU_ADD;
            alu_source_2_o   = ALU_SCR2_IMM;
            immediate_type_o = IMM_I;
            
            mem_sign_extend_o = !funct3[2];
            
            reg_mem_wen_o = 1'b1;
            
            unique case (funct3)
                3'b000, 3'b100: mem_data_type_o = BYTE;      // lb, lbu
                3'b001, 3'b101: mem_data_type_o = HALF_WORD; // lh, lhu
                3'b010        : mem_data_type_o = WORD;      // lw
                default: illegal_instr_o = 1'b1;
            endcase
        end
            
        OPCODE_STORE: begin
            alu_operation_o  = ALU_ADD;
            alu_source_2_o   = ALU_SCR2_IMM;
            immediate_type_o = IMM_S;
            
            mem_wen_o = 1'b1;
            
            unique case (funct3)
                3'b000: mem_data_type_o = BYTE;      // sb
                3'b001: mem_data_type_o = HALF_WORD; // sh
                3'b010: mem_data_type_o = WORD;      // sw
                default: illegal_instr_o = 1'b1;
            endcase
        end
        
        /////////////////////////////////////////////
        //////////    Jumps / Branches    ///////////
        /////////////////////////////////////////////
        OPCODE_BRANCH: begin
            // ALU does the comparison
            // The branch target has a dedicated adder in ID stage
            immediate_type_o = IMM_B;
            
            pc_source_o = PC_BRANCH;
            is_branch_o = 1'b1;
            
            unique case (funct3)
                3'b000: alu_operation_o = ALU_SEQ;  // beq
                3'b001: alu_operation_o = ALU_SNE;  // bne
                3'b100: alu_operation_o = ALU_SLT;  // blt
                3'b101: alu_operation_o = ALU_SGE;  // bge
                3'b110: alu_operation_o = ALU_SLTU; // bltu
                3'b111: alu_operation_o = ALU_SGEU; // bgeu
                default: illegal_instr_o = 1'b1;
            endcase
        end
        
        OPCODE_JAL: begin // jal
            // ALU calculates PC+4 or PC+2
            // The jump target has a dedicated adder in ID stage
            alu_operation_o  = ALU_ADD;
            alu_source_1_o   = ALU_SCR1_PC;
            alu_source_2_o   = ALU_SCR2_4_OR_2;
            immediate_type_o = IMM_J;
            
            reg_alu_wen_o  = 1'b1;
            
            pc_source_o  = PC_JAL;
        end
        
        OPCODE_JALR: begin // jalr
            // ALU calculates PC+4 or PC+2
            // The jump target has a dedicated adder in ID stage
            alu_operation_o  = ALU_ADD;
            alu_source_1_o   = ALU_SCR1_PC;
            alu_source_2_o   = ALU_SCR2_4_OR_2;
            immediate_type_o = IMM_I;
            
            reg_alu_wen_o  = 1'b1;
            
            pc_source_o  = PC_JALR;
            
            if (funct3 != 3'b000)
                illegal_instr_o = 1'b1;
        end
        
        /////////////////////////////////////////////
        /////////////      System       /////////////
        /////////////////////////////////////////////
        OPCODE_SYSTEM: begin
            // Non CSR related SYSTEM instructions
            if (funct3 == '0) begin
                if ({instr_i[19:15], instr_i[11:7]} == '0) begin
                    unique case (instr_i[31:20])
                        12'h000: begin // ecall
                            illegal_instr_o = 1'b1;
                        end
                        12'h001: begin // ebreak
                            illegal_instr_o = 1'b1;
                        end
                        12'h302: begin // mret
                            is_mret_o = 1'b1;
                        end
                        12'h002: begin // uret
                            illegal_instr_o = 1'b1;
                        end
                        12'h7b2: begin // dret
                            illegal_instr_o = 1'b1;
                        end
                        12'h105: begin // wfi
                            illegal_instr_o = 1'b1;
                        end
                        default: illegal_instr_o = 1'b1;
                    endcase
                end
                else begin
                    illegal_instr_o = 1'b1;
                end
            end
            // Instructions that read/modify CSRs
            else begin 
                csr_access_o  = 1'b1;
                reg_alu_wen_o = 1'b1;
                alu_source_2_o = ALU_SCR2_IMM;
                unique case (funct3)
                    3'b001: begin // csrrw
                        csr_op_o = CSR_WRITE;
                        
                    end
                    3'b010: begin // csrrs
                        csr_op_o = (instr_i[19:15] == 5'b0) ? (CSR_READ) : (CSR_SET);
                        
                    end
                    3'b011: begin // csrrc
                        csr_op_o = (instr_i[19:15] == 5'b0) ? (CSR_READ) : (CSR_CLEAR);
                        
                    end
                    3'b101: begin // csrrwi
                        csr_op_o       = CSR_WRITE;
                        alu_source_1_o = ALU_SCR1_IMM_CSR;
                    end
                    3'b110: begin // csrrsi
                        csr_op_o = (instr_i[19:15] == 5'b0) ? (CSR_READ) : (CSR_SET);
                        alu_source_1_o = ALU_SCR1_IMM_CSR;
                    end
                    3'b111: begin // csrrci
                        csr_op_o = (instr_i[19:15] == 5'b0) ? (CSR_READ) : (CSR_CLEAR);
                        alu_source_1_o = ALU_SCR1_IMM_CSR;
                    end
                    default: illegal_instr_o = 1'b1;
                endcase
                
                // Check privilege level
                // if (instr_i[29:28] > current_priv_lvl_i) begin
                //     illegal_instr_o = 1'b1;
                // end
                
                // Determine if CSR access is illegal
                case (instr_i[31:20])
                    CSR_MISA: ;
        
                    CSR_MVENDORID,
                    CSR_MARCHID,
                    CSR_MIMPID,
                    CSR_MHARTID: if (csr_op_o != CSR_READ) illegal_instr_o = 1'b1;
                    
                    CSR_MSTATUS,
                    CSR_MIE,
                    CSR_MTVEC: ;
                    
                    CSR_MEPC,
                    CSR_MCAUSE: ;
                    
                    default: illegal_instr_o = 1'b1;
                endcase
            end
        end
        
        default: illegal_instr_o = 1'b1;
    endcase
end
    
endmodule