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

logic [1:0] opcode_C;
logic [5:0] funct6_C;
logic [3:0] funct4_C;
logic [2:0] funct3_C;
logic [1:0] funct2_C;
logic [4:0] rs1_addr_C, rs2_addr_C, rd_addr_C;

assign funct7 = instr_i[31:25];
assign funct3 = instr_i[14:12];
assign opcode = instr_i[ 6: 0];

assign opcode_C = instr_i[ 1: 0];
assign funct6_C = instr_i[15:10];
assign funct4_C = instr_i[15:12];
assign funct3_C = instr_i[15:13];
assign funct2_C = instr_i[ 6: 5];

wire is_compressed = (instr_i[1:0] != 2'b11);

assign rs1_addr_o = (opcode[1] && opcode[0]) ? instr_i[19:15] : rs1_addr_C;
assign rs2_addr_o = (opcode[1] && opcode[0]) ? instr_i[24:20] : rs2_addr_C;
assign rd_addr_o  = (opcode[1] && opcode[0]) ? instr_i[11: 7] : rd_addr_C;

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
    
    rs1_addr_C = 5'd0;
    rs2_addr_C = 5'd0;
    rd_addr_C = 5'd0;
    
    if (ISA_C && is_compressed) begin

        case (opcode_C)
        OPCODE_RVC_1: begin
            unique case (instr_i[15:13])
                
                /*3'b000: begin
                    // C.ADDI4SPN
                    rd_addr_C = {2'b01, instr_i[4:2]};
                    //rs1_addr_C =;
                    //rs2_addr_C =;
                    //imm = IMM_CLS;
                    alu_source_1_o = ALU_SCR1_ZERO;
                    alu_source_2_o = ALU_SCR2_IMM;
                    alu_operation_o = ALU_ADD; // ADD
                    reg_alu_wen_o = 1'b1;

                end*/

                3'b001: begin
                    // C.FLD
                    reg_mem_wen_o = 1'b1;
                    rd_addr_C = {2'b01, instr_i[4:2]};
                    rs1_addr_C ={2'b01, instr_i[9:7]};
                    

                    immediate_type_o = IMM_CLS;

                    alu_source_2_o = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;

                end

                3'b010: begin
                    // C.LW
                    reg_mem_wen_o = 1'b1;
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rd_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;
                    
                    alu_source_2_o   = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;
                end

                3'b011: begin
                    // C.FLW

                    reg_mem_wen_o = 1'b1;
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rd_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;

                end

                /*3'b101:begin // C.FSD  

                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o  = ALU_ADD;

                    // DOUBLE

                end*/

                3'b110: begin
                    // C.SW
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o = ALU_ADD; // STORE

                    mem_wen_o = 1'b1;
                    mem_data_type_o = WORD;
                    mem_sign_extend_o = 1'b0;

                end

                3'b111: begin
                    // C.FSW
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o = ALU_ADD; // STORE

                    mem_wen_o = 1'b1;
                    mem_data_type_o = WORD;
                    mem_sign_extend_o = 1'b0;

                end
                
                default: begin
                    illegal_instr_o = 1'b1;
                end

            endcase
        end

        OPCODE_RVC_2: begin
            case (instr_i[15:13]) // Concluido
                3'b000: begin
                    // C.ADDI
                    reg_alu_wen_o = 1'b1;
                    rd_addr_C = instr_i[11:7];
                    rs1_addr_C = instr_i[11:7];
                    
                    alu_source_2_o = ALU_SCR2_IMM;
                    alu_source_1_o = ALU_SCR1_RS1;
                    reg_alu_wen_o  = 1'b1;
                    
                    alu_operation_o  = ALU_ADD;

                    immediate_type_o = IMM_CI;

                end

                3'b001: begin // Concluido
                    // C.JAL
                    alu_operation_o  = ALU_ADD;

                    alu_source_1_o   = ALU_SCR1_PC;
                    alu_source_2_o   = ALU_SCR2_4_OR_2;

                    immediate_type_o = IMM_CJ;

                    reg_alu_wen_o  = 1'b1;

                    pc_source_o  = PC_JALR;
                    
                end

                3'b010: begin
                    // C.LI
                    rd_addr_C = instr_i[11:7];
                    
                    alu_operation_o  = ALU_ADD;

                    reg_mem_wen_o = 1'b1;
                    

                    rs1_addr_C = {2'b01, instr_i[9:7]};

                    immediate_type_o = IMM_CI;

                    alu_source_2_o   = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;
                end

                3'b011: begin
                    if (instr_i[11:7] == 5'b00010) begin
                        // C.ADDI16SP

                        rd_addr_C = 5'b00010;
                        reg_alu_wen_o = 1'b1;

                        immediate_type_o = IMM_CI;

                        alu_source_2_o   = ALU_SCR2_IMM;
                        alu_operation_o = ALU_ADD;
                        

                    end else begin // Não ENTENDI COMO FAZER
                        // C.LUI
                        rd_addr_C = instr_i[11:7];
                        reg_alu_wen_o  = 1'b1; // Estou na duvida sobre isso aqui!

                        alu_operation_o  = ALU_ADD;
                        alu_source_1_o   = ALU_SCR1_ZERO;
                        alu_source_2_o   = ALU_SCR2_IMM;
                        immediate_type_o = IMM_CLUI;
                        
                        

                    end
                end

                3'b100: begin
                    case (instr_i[11:10])
                        2'b00: begin
                            // C.SRLI
                            rd_addr_C = instr_i[9:7];
                            reg_alu_wen_o = 1'b1;

                            immediate_type_o = IMM_CI;
                            
                            alu_operation_o = ALU_SRL; // SRL
                        end
                        2'b01: begin
                            // C.SRAI
                            rd_addr_C = instr_i[9:7];
                            reg_alu_wen_o = 1'b1;

                            immediate_type_o = IMM_CI;

                            alu_operation_o = ALU_SRA; // SRA
                        end
                        2'b10: begin
                            // C.ANDI
                            rd_addr_C = instr_i[9:7];
                            reg_alu_wen_o = 1'b1;

                            immediate_type_o = IMM_CI; // sign-extend

                            alu_operation_o = ALU_AND; // AND
                        end
                        2'b11: begin
                            case (instr_i[6:5])
                                2'b00: begin
                                    // C.SUB
                                    rd_addr_C = {2'b01, instr_i[4:2]};
                                    reg_alu_wen_o = 1'b1;
                                    rs2_addr_C = {2'b01, instr_i[9:7]};
                                    alu_operation_o = ALU_SUB; // SUB
                                end
                                2'b01: begin
                                    // C.XOR
                                    rd_addr_C = {2'b01, instr_i[4:2]};
                                    reg_alu_wen_o = 1'b1;
                                    rs2_addr_C = {2'b01, instr_i[9:7]};
                                    alu_operation_o = ALU_XOR; // XOR
                                end
                                2'b10: begin
                                    // C.OR
                                    rd_addr_C = {2'b01, instr_i[4:2]};
                                    reg_alu_wen_o = 1'b1;
                                    rs2_addr_C = {2'b01, instr_i[9:7]};
                                    alu_operation_o = ALU_OR; // OR
                                end
                                2'b11: begin
                                    // C.AND
                                    rd_addr_C = {2'b01, instr_i[4:2]};
                                    reg_alu_wen_o = 1'b1;
                                    rs2_addr_C = {2'b01, instr_i[9:7]};
                                    alu_operation_o = ALU_AND; // AND
                                end
                            endcase
                        end
                    endcase
                end
                3'b101: begin //PAREI AQUI
                    // C.J
                    immediate_type_o = IMM_CJ;
                    alu_operation_o = ALU_ADD; // JUMP
                    alu_source_1_o = ALU_SCR1_PC;
                    alu_source_2_o = ALU_SCR2_IMM;
                    
                    reg_alu_wen_o  = 1'b1;
            
                    pc_source_o  = PC_JAL;
                    // FALTA COISA EU ACHO
                end
                3'b110: begin
                    // C.BEQZ
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    immediate_type_o = IMM_CB;
                    alu_operation_o = ALU_SEQ; // BEQ

                end
                3'b111: begin
                    // C.BNEZ
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    immediate_type_o = IMM_CB;
                    alu_operation_o = ALU_SNE; // BNE
                end
            endcase  
            

        end

        OPCODE_RVC_3: begin
            case (funct3_C)
                3'b000: begin //CSLLi
                    alu_source_2_o  = ALU_SCR2_IMM;
                    reg_alu_wen_o   = 1'b1;
                    alu_operation_o = ALU_SLL;
                    
                    immediate_type_o = IMM_CI;

                    rd_addr_C  = instr_i[11:7];
                    rs1_addr_C = instr_i[11:7];
                end
                3'b01x: begin //CLs
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_I;
                    mem_data_type_o  = WORD;
                    //immediate_type_o = IMM_I;
                    reg_mem_wen_o    = 1'b1;
                    
                    immediate_type_o = IMM_CSPL;

                    rs1_addr_C = 5'd2; //x2
                    rd_addr_C  = instr_i[11:7];
                    if (funct3_C[0])
                        mem_wen_o = 1'b1; //C_FLWSP?

                end
                3'b100: begin
                    if (funct4_C[0] == 1'd0) begin
                        if (instr_i[11:7] == 5'd0) illegal_instr_o = 1'b1; else begin
                            if (instr_i[6:2] == 5'd0) begin //C_JR
                                // ALU calculates PC+4 or PC+2
                                // The jump target has a dedicated adder in ID stage
                            
                                alu_operation_o  = ALU_ADD;
                                alu_source_1_o   = ALU_SCR1_PC;
                                alu_source_2_o   = ALU_SCR2_4_OR_2;
                                //immediate_type_o = IMM_I;
                                reg_alu_wen_o  = 1'b1;
                                pc_source_o    = PC_JALR;

                                
                                immediate_type_o = IMM_CJR;

                                rs1_addr_C = instr_i[11:7];
                                rs2_addr_C = 5'd0;
                                rd_addr_C  = 5'd0;

                            end
                            else begin //C_MV
                                reg_alu_wen_o   = 1'b1;
                                alu_operation_o = ALU_ADD;

                                rd_addr_C  = instr_i[11:7];
                                rs1_addr_C = 5'd0; //zero (x0)
                                rs2_addr_C = instr_i[6:2];
                            end
                        end

                    end
                    else begin
                        if (instr_i[11:2] == 10'd0) illegal_instr_o = 1'b1; else begin //C_BREAK
                            if (instr_i[6:2] == 5'd0) begin //C_JALR
                                // ALU calculates PC+4 or PC+2
                                // The jump target has a dedicated adder in ID stage
                            
                                alu_operation_o  = ALU_ADD;
                                alu_source_1_o   = ALU_SCR1_PC;
                                alu_source_2_o   = ALU_SCR2_4_OR_2;
                                //immediate_type_o = IMM_I;
                                reg_alu_wen_o    = 1'b1;
                                pc_source_o      = PC_JALR;

                                immediate_type_o = IMM_CJR;

                                rs1_addr_C = instr_i[11:7];
                                rs2_addr_C = 5'd1;
                                rd_addr_C  = 5'd1;

                            end
                            else begin //C_ADD
                                reg_alu_wen_o   = 1'b1;
                                alu_operation_o = ALU_ADD;

                                rd_addr_C  = instr_i[11:7];
                                rs1_addr_C = instr_i[11:7];
                                rs2_addr_C = instr_i[6:2];
                            end
                        end
                    end
                end
                3'b11x: begin //C_SWSP
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    mem_data_type_o  = WORD;
                    //immediate_type_o = IMM_S;
                    mem_wen_o        = 1'b1;

                    immediate_type_o = IMM_CSPS;

                    rs1_addr_C = 5'd2; //x2
                    rs2_addr_C = instr_i[6:2];
                    if (funct3_C[0])
                        mem_wen_o = 1'b1; //C_FSWSP?
                end
                default: illegal_instr_o = 1'b1;
            endcase
        end
        endcase
    end
    else begin
        
    unique case (opcode)
        /////////////////////////////////////////////
        /////////////        ALU        /////////////
        /////////////////////////////////////////////
        OPCODE_OP: begin
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
        
        /////////////////////////////////////////////
        /////////////       RVC         /////////////
        /////////////////////////////////////////////
        
        // OPCODE_RVC_1: begin
        //     unique case (instr_i[15:13])
                
        //         /*3'b000: begin
        //             // C.ADDI4SPN
        //             rd_addr_C = {2'b01, instr_i[4:2]};
        //             //rs1_addr_C =;
        //             //rs2_addr_C =;
        //             //imm = IMM_CLS;
        //             alu_source_1_o = ALU_SCR1_ZERO;
        //             alu_source_2_o = ALU_SCR2_IMM;
        //             alu_operation_o = ALU_ADD; // ADD
        //             reg_alu_wen_o = 1'b1;

        //         end*/

        //         3'b001: begin
        //             // C.FLD
        //             reg_mem_wen_o = 1'b1;
        //             rd_addr_C = {2'b01, instr_i[4:2]};
        //             rs1_addr_C ={2'b01, instr_i[9:7]};
                    

        //             immediate_type_o = IMM_CLS;

        //             alu_source_2_o = ALU_SCR2_IMM;
        //             alu_operation_o  = ALU_ADD;

        //         end

        //         3'b010: begin
        //             // C.LW
        //             reg_mem_wen_o = 1'b1;
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             rd_addr_C = {2'b01, instr_i[4:2]};

        //             immediate_type_o = IMM_CLS;
                    
        //             alu_source_2_o   = ALU_SCR2_IMM;
        //             alu_operation_o  = ALU_ADD;
        //         end

        //         3'b011: begin
        //             // C.FLW

        //             reg_mem_wen_o = 1'b1;
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             rd_addr_C = {2'b01, instr_i[4:2]};

        //             immediate_type_o = IMM_CLS;

        //             alu_operation_o  = ALU_ADD;
        //             alu_source_2_o   = ALU_SCR2_IMM;

        //         end

        //         /*3'b101:begin // C.FSD  

        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             rs2_addr_C = {2'b01, instr_i[4:2]};

        //             immediate_type_o = IMM_CLS;

        //             alu_operation_o  = ALU_ADD;

        //             // DOUBLE

        //         end*/

        //         3'b110: begin
        //             // C.SW
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             rs2_addr_C = {2'b01, instr_i[4:2]};

        //             immediate_type_o = IMM_CLS;

        //             alu_operation_o = ALU_ADD; // STORE

        //             mem_wen_o = 1'b1;
        //             mem_data_type_o = WORD;
        //             mem_sign_extend_o = 1'b0;

        //         end

        //         3'b111: begin
        //             // C.FSW
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             rs2_addr_C = {2'b01, instr_i[4:2]};

        //             immediate_type_o = IMM_CLS;

        //             alu_operation_o = ALU_ADD; // STORE

        //             mem_wen_o = 1'b1;
        //             mem_data_type_o = WORD;
        //             mem_sign_extend_o = 1'b0;

        //         end
                
        //         default: begin
        //             illegal_instr_o = 1'b1;
        //         end

        //     endcase
        // end

        // OPCODE_RVC_2: begin
        //     case (instr_i[15:13]) // Concluido
        //         3'b000: begin
        //             // C.ADDI
        //             reg_alu_wen_o = 1'b1;
        //             rd_addr_C = instr_i[11:7];
        //             rs1_addr_C = instr_i[11:7];
                    
        //             alu_source_2_o = ALU_SCR2_IMM;
        //             alu_source_1_o = ALU_SCR1_RS1;
        //             reg_alu_wen_o  = 1'b1;
                    
        //             alu_operation_o  = ALU_ADD;

        //             immediate_type_o = IMM_CI;

        //         end

        //         3'b001: begin // Concluido
        //             // C.JAL
        //             alu_operation_o  = ALU_ADD;

        //             alu_source_1_o   = ALU_SCR1_PC;
        //             alu_source_2_o   = ALU_SCR2_4_OR_2;

        //             immediate_type_o = IMM_CJ;

        //             reg_alu_wen_o  = 1'b1;

        //             pc_source_o  = PC_JALR;
                    
        //         end

        //         3'b010: begin
        //             // C.LI
        //             rd_addr_C = instr_i[11:7];
                    
        //             alu_operation_o  = ALU_ADD;

        //             reg_mem_wen_o = 1'b1;
                    

        //             rs1_addr_C = {2'b01, instr_i[9:7]};

        //             immediate_type_o = IMM_CI;

        //             alu_source_2_o   = ALU_SCR2_IMM;
        //             alu_operation_o  = ALU_ADD;
        //         end

        //         3'b011: begin
        //             if (instr_i[11:7] == 5'b00010) begin
        //                 // C.ADDI16SP

        //                 rd_addr_C = 5'b00010;
        //                 reg_alu_wen_o = 1'b1;

        //                 immediate_type_o = IMM_CI;

        //                 alu_source_2_o   = ALU_SCR2_IMM;
        //                 alu_operation_o = ALU_ADD;
                        

        //             end else begin // Não ENTENDI COMO FAZER
        //                 // C.LUI
        //                 rd_addr_C = instr_i[11:7];
        //                 reg_alu_wen_o  = 1'b1; // Estou na duvida sobre isso aqui!

        //                 alu_operation_o  = ALU_ADD;
        //                 alu_source_1_o   = ALU_SCR1_ZERO;
        //                 alu_source_2_o   = ALU_SCR2_IMM;
        //                 immediate_type_o = IMM_CLUI;
                        
                        

        //             end
        //         end

        //         3'b100: begin
        //             case (instr_i[11:10])
        //                 2'b00: begin
        //                     // C.SRLI
        //                     rd_addr_C = instr_i[9:7];
        //                     reg_alu_wen_o = 1'b1;

        //                     immediate_type_o = IMM_CI;
                            
        //                     alu_operation_o = ALU_SRL; // SRL
        //                 end
        //                 2'b01: begin
        //                     // C.SRAI
        //                     rd_addr_C = instr_i[9:7];
        //                     reg_alu_wen_o = 1'b1;

        //                     immediate_type_o = IMM_CI;

        //                     alu_operation_o = ALU_SRA; // SRA
        //                 end
        //                 2'b10: begin
        //                     // C.ANDI
        //                     rd_addr_C = instr_i[9:7];
        //                     reg_alu_wen_o = 1'b1;

        //                     immediate_type_o = IMM_CI; // sign-extend

        //                     alu_operation_o = ALU_AND; // AND
        //                 end
        //                 2'b11: begin
        //                     case (instr_i[6:5])
        //                         2'b00: begin
        //                             // C.SUB
        //                             rd_addr_C = {2'b01, instr_i[4:2]};
        //                             reg_alu_wen_o = 1'b1;
        //                             rs2_addr_C = {2'b01, instr_i[9:7]};
        //                             alu_operation_o = ALU_SUB; // SUB
        //                         end
        //                         2'b01: begin
        //                             // C.XOR
        //                             rd_addr_C = {2'b01, instr_i[4:2]};
        //                             reg_alu_wen_o = 1'b1;
        //                             rs2_addr_C = {2'b01, instr_i[9:7]};
        //                             alu_operation_o = ALU_XOR; // XOR
        //                         end
        //                         2'b10: begin
        //                             // C.OR
        //                             rd_addr_C = {2'b01, instr_i[4:2]};
        //                             reg_alu_wen_o = 1'b1;
        //                             rs2_addr_C = {2'b01, instr_i[9:7]};
        //                             alu_operation_o = ALU_OR; // OR
        //                         end
        //                         2'b11: begin
        //                             // C.AND
        //                             rd_addr_C = {2'b01, instr_i[4:2]};
        //                             reg_alu_wen_o = 1'b1;
        //                             rs2_addr_C = {2'b01, instr_i[9:7]};
        //                             alu_operation_o = ALU_AND; // AND
        //                         end
        //                     endcase
        //                 end
        //             endcase
        //         end
        //         3'b101: begin //PAREI AQUI
        //             // C.J
        //             immediate_type_o = IMM_CJ;
        //             alu_operation_o = ALU_ADD; // JUMP
        //             alu_source_1_o = ALU_SCR1_PC;
        //             alu_source_2_o = ALU_SCR2_IMM;
                    
        //             reg_alu_wen_o  = 1'b1;
            
        //             pc_source_o  = PC_JAL;
        //             // FALTA COISA EU ACHO
        //         end
        //         3'b110: begin
        //             // C.BEQZ
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             immediate_type_o = IMM_CB;
        //             alu_operation_o = ALU_SEQ; // BEQ

        //         end
        //         3'b111: begin
        //             // C.BNEZ
        //             rs1_addr_C = {2'b01, instr_i[9:7]};
        //             immediate_type_o = IMM_CB;
        //             alu_operation_o = ALU_SNE; // BNE
        //         end
        //     endcase  
            

        // end

        // OPCODE_RVC_3: begin
        //     case (funct3_C)
        //         3'b000: begin //CSLLi
        //             alu_source_2_o  = ALU_SCR2_IMM;
        //             reg_alu_wen_o   = 1'b1;
        //             alu_operation_o = ALU_SLL;
                    
        //             immediate_type_o = IMM_CI;

        //             rd_addr_C  = instr_i[11:7];
        //             rs1_addr_C = instr_i[11:7];
        //         end
        //         3'b01x: begin //CLs
        //             alu_operation_o  = ALU_ADD;
        //             alu_source_2_o   = ALU_SCR2_IMM;
        //             immediate_type_o = IMM_I;
        //             mem_data_type_o  = WORD;
        //             //immediate_type_o = IMM_I;
        //             reg_mem_wen_o    = 1'b1;
                    
        //             immediate_type_o = IMM_CSPL;

        //             rs1_addr_C = 5'd2; //x2
        //             rd_addr_C  = instr_i[11:7];
        //             if (funct3_C[0])
        //                 mem_wen_o = 1'b1; //C_FLWSP?

        //         end
        //         3'b100: begin
        //             if (funct4_C[0] == 1'd0) begin
        //                 if (instr_i[11:7] == 5'd0) illegal_instr_o = 1'b1; else begin
        //                     if (instr_i[6:2] == 5'd0) begin //C_JR
        //                         // ALU calculates PC+4 or PC+2
        //                         // The jump target has a dedicated adder in ID stage
                            
        //                         alu_operation_o  = ALU_ADD;
        //                         alu_source_1_o   = ALU_SCR1_PC;
        //                         alu_source_2_o   = ALU_SCR2_4_OR_2;
        //                         //immediate_type_o = IMM_I;
        //                         reg_alu_wen_o  = 1'b1;
        //                         pc_source_o    = PC_JALR;

                                
        //                         immediate_type_o = IMM_CJR;

        //                         rs1_addr_C = instr_i[11:7];
        //                         rs2_addr_C = 5'd0;
        //                         rd_addr_C  = 5'd0;

        //                     end
        //                     else begin //C_MV
        //                         reg_alu_wen_o   = 1'b1;
        //                         alu_operation_o = ALU_ADD;

        //                         rd_addr_C  = instr_i[11:7];
        //                         rs1_addr_C = 5'd0; //zero (x0)
        //                         rs2_addr_C = instr_i[6:2];
        //                     end
        //                 end

        //             end
        //             else begin
        //                 if (instr_i[11:2] == 10'd0) illegal_instr_o = 1'b1; else begin //C_BREAK
        //                     if (instr_i[6:2] == 5'd0) begin //C_JALR
        //                         // ALU calculates PC+4 or PC+2
        //                         // The jump target has a dedicated adder in ID stage
                            
        //                         alu_operation_o  = ALU_ADD;
        //                         alu_source_1_o   = ALU_SCR1_PC;
        //                         alu_source_2_o   = ALU_SCR2_4_OR_2;
        //                         //immediate_type_o = IMM_I;
        //                         reg_alu_wen_o    = 1'b1;
        //                         pc_source_o      = PC_JALR;

        //                         immediate_type_o = IMM_CJR;

        //                         rs1_addr_C = instr_i[11:7];
        //                         rs2_addr_C = 5'd1;
        //                         rd_addr_C  = 5'd1;

        //                     end
        //                     else begin //C_ADD
        //                         reg_alu_wen_o   = 1'b1;
        //                         alu_operation_o = ALU_ADD;

        //                         rd_addr_C  = instr_i[11:7];
        //                         rs1_addr_C = instr_i[11:7];
        //                         rs2_addr_C = instr_i[6:2];
        //                     end
        //                 end
        //             end
        //         end
        //         3'b11x: begin //C_SWSP
        //             alu_operation_o  = ALU_ADD;
        //             alu_source_2_o   = ALU_SCR2_IMM;
        //             mem_data_type_o  = WORD;
        //             //immediate_type_o = IMM_S;
        //             mem_wen_o        = 1'b1;

        //             immediate_type_o = IMM_CSPS;

        //             rs1_addr_C = 5'd2; //x2
        //             rs2_addr_C = instr_i[6:2];
        //             if (funct3_C[0])
        //                 mem_wen_o = 1'b1; //C_FSWSP?
        //         end
        //         default: illegal_instr_o = 1'b1;
        //     endcase
        // end


        default: illegal_instr_o = 1'b1;
    endcase
    
    end
end
    
endmodule
