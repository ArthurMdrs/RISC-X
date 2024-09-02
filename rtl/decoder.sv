module decoder import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 1
) (
    // ALU related signals
    output alu_operation_t    alu_operation_o,
    output alu_source_1_t     alu_source_1_o, 
    output alu_source_2_t     alu_source_2_o, 
    output alu_source_3_t     alu_source_3_o, 
    output immediate_source_t immediate_type_o,
    // output logic              alu_en_o, // Disable ALU to save some power?
    output alu_result_mux_t   alu_result_mux_o,
    
    // Source/destiny general purpose registers
    output logic [4:0] rs1_addr_o,
    output logic [4:0] rs2_addr_o,
    output logic [4:0] rs3_addr_o,
    output logic [4:0] rd_addr_o,
    output reg_bank_mux_t rs1_src_bank_o,
    output reg_bank_mux_t rs2_src_bank_o,
    output reg_bank_mux_t rs3_src_bank_o,
    output reg_bank_mux_t rd_dst_bank_o,
    // TODO: really implement rsx_is_used (use to make better forwarding/stalls and in RVFI)
    output logic rs1_is_used_o,
    output logic rs2_is_used_o,
    output logic rs3_is_used_o,
    
    // Memory access related signals
    output logic       mem_wen_o,
    output data_type_t mem_data_type_o,
    output logic       mem_sign_extend_o,
    
    // Write enable for ALU and mem access operations
    output logic reg_alu_wen_o, 
    output logic reg_mem_wen_o, 
    
    // Control transfer related signals
    output pc_source_t pc_source_o, 
    output logic       is_branch_o,
    // TODO: create a is_jump so pc_controller doesn't have to use pc_source
    
    // CSR related signals
    output logic           csr_access_o,
    output csr_operation_t csr_op_o,
    
    // Indicate MRET
    output logic is_mret_o,
    
    // Decoded an illegal instruction
    output logic illegal_instr_o,
    
    // Instruction to be decoded
    input  logic [31:0] instr_i,
    input  logic        is_compressed_i,


    ////////FPU/////////////////
    output logic [2:0] fpu_rnd_mode_o,
    output logic [3:0] fpu_op_o,
    output logic       fpu_op_mod_o,
    output logic       fpu_req_o,
    
    // output logic [4:0] rs3_addr_F_o,
    // output logic [4:0] is_store_o
    //output logic is_immediate_F
    output logic           csr_status_o // Adicionado

    //input logic fs_off_i;

    //output logic [31:0]  fpu_dst_fmt_o,   // fpu destination format
    //output logic [31:0]  fpu_src_fmt_o,   // fpu source format
    //output logic [31:0] fpu_int_fmt_o
);

logic [6:0] funct7;
logic [2:0] funct3;
logic [6:0] opcode;

logic [1:0] opcode_C;
logic [3:0] funct4_C;
logic [2:0] funct3_C;
logic [1:0] funct2_C;
logic [4:0] rs1_addr_C, rs2_addr_C, rd_addr_C;

`ifdef JASPER
`default_nettype none
`endif

assign funct7 = instr_i[31:25];
assign funct3 = instr_i[14:12];
assign opcode = instr_i[ 6: 0];

assign opcode_C = instr_i[ 1: 0];
assign funct4_C = instr_i[15:12];
assign funct3_C = instr_i[15:13];
assign funct2_C = instr_i[ 6: 5];

wire is_compressed_int = is_compressed_i && ISA_C;

// TODO: move all rs and rd logic to the always_comb
assign rs1_addr_o = (is_compressed_int) ? (rs1_addr_C) : (instr_i[19:15]);
assign rs2_addr_o = (is_compressed_int) ? (rs2_addr_C) : (instr_i[24:20]);
assign rd_addr_o  = (is_compressed_int) ? (rd_addr_C ) : (instr_i[11: 7]);



always_comb begin
    alu_operation_o  = ALU_ADD;
    alu_source_1_o   = ALU_SCR1_RS1;
    alu_source_2_o   = ALU_SCR2_RS2;
    alu_source_3_o   = ALU_SCR3_RS3;
    immediate_type_o = IMM_I;
    alu_result_mux_o = BASIC_ALU_RESULT;
    
    rs3_addr_o = instr_i[31:27];
    rs1_src_bank_o = X_REG;
    rs2_src_bank_o = X_REG;
    rs3_src_bank_o = F_REG;
    rd_dst_bank_o  = X_REG;
    rs1_is_used_o  = 1'b0;
    rs2_is_used_o  = 1'b0;
    rs3_is_used_o  = 1'b0;
    
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
    
    rs1_addr_C = instr_i[11:7];
    rs2_addr_C = instr_i[ 6:2];
    rd_addr_C  = instr_i[11:7];

    //F
    fpu_req_o = 1'b0;
    
    
    fpu_rnd_mode_o  = instr_i[14:12];
    fpu_op_o = fpnew_pkg::SGNJ;
    fpu_op_mod_o = 1'b0;
    //is_immediate_F = 1'b0;
    csr_status_o = 1'b0;

    
    if (is_compressed_int) begin 
    unique case (opcode_C)
        OPCODE_RVC_0: begin
            unique case (funct3_C)
                3'b000: begin // c.addi4spn
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CIW;
                    
                    reg_alu_wen_o = 1'b1;
                    
                    rs1_addr_C = 5'd2; // x2/sp
                    rd_addr_C  = {2'b01, instr_i[4:2]};
                    
                    // Code points with imm=0 are reserved
                    if (instr_i[12:5] == 8'd0)
                        illegal_instr_o = 1'b1;
                end
                /*3'b001: begin // c.fld
                    reg_mem_wen_o = 1'b1;
                    rd_addr_C = {2'b01, instr_i[4:2]};
                    rs1_addr_C ={2'b01, instr_i[9:7]};

                    immediate_type_o = IMM_CLS;

                    alu_source_2_o = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;
                end*/
                3'b010: begin // c.lw
                    alu_source_2_o   = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;
                    immediate_type_o = IMM_CLS;

                    reg_mem_wen_o = 1'b1;
                    
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rd_addr_C  = {2'b01, instr_i[4:2]};
                end
                /*3'b011: begin // c.flw
                    reg_mem_wen_o = 1'b1;
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rd_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                end*/
                /*3'b101:begin // c.fsd
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o  = ALU_ADD;

                    // DOUBLE
                end*/
                3'b110: begin // c.sw
                    alu_source_2_o   = ALU_SCR2_IMM;
                    alu_operation_o  = ALU_ADD;
                    immediate_type_o = IMM_CLS;

                    mem_wen_o = 1'b1;

                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};
                end
                /*3'b111: begin // c.fsw
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = {2'b01, instr_i[4:2]};

                    immediate_type_o = IMM_CLS;

                    alu_operation_o = ALU_ADD; // STORE

                    mem_wen_o = 1'b1;
                    mem_data_type_o = WORD;
                    mem_sign_extend_o = 1'b0;
                end*/
                default: illegal_instr_o = 1'b1;
            endcase
        end

        OPCODE_RVC_1: begin
            unique case (funct3_C)
                3'b000: begin // c.addi
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CI;
                    
                    reg_alu_wen_o = 1'b1;

                    // Code points with imm=0 are hints
                end
                3'b001: begin // c.jal
                    // ALU calculates PC+2
                    // The jump target has a dedicated adder in ID stage
                    alu_operation_o  = ALU_ADD;
                    alu_source_1_o   = ALU_SCR1_PC;
                    alu_source_2_o   = ALU_SCR2_4_OR_2;
                    immediate_type_o = IMM_CJ;

                    reg_alu_wen_o  = 1'b1;

                    pc_source_o  = PC_JAL;
                    
                    rd_addr_C = 5'd1; // x1/ra
                end
                3'b010: begin // c.li
                    alu_operation_o  = ALU_ADD;
                    alu_source_1_o   = ALU_SCR1_ZERO;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CI;
                    
                    reg_alu_wen_o = 1'b1;
                    
                    // Code points with rd=0 are hints
                end
                3'b011: begin
                    if (rd_addr_C == 5'd2) begin // c.addi16sp
                        alu_operation_o  = ALU_ADD;
                        alu_source_2_o   = ALU_SCR2_IMM;
                        immediate_type_o = IMM_C16;
                        
                        reg_alu_wen_o = 1'b1;

                        // Code points with imm=0 are reserved
                        if ({instr_i[12],instr_i[6:2]} == 6'd0) // Move this before the if?
                            illegal_instr_o = 1'b1;
                    end else begin // c.lui
                        alu_operation_o  = ALU_ADD;
                        alu_source_1_o   = ALU_SCR1_ZERO;
                        alu_source_2_o   = ALU_SCR2_IMM;
                        immediate_type_o = IMM_CLUI;
                        
                        reg_alu_wen_o  = 1'b1;
                            
                        // Code points with imm=0 are reserved
                        if ({instr_i[12],instr_i[6:2]} == 6'd0) // Move this before the if?
                            illegal_instr_o = 1'b1;
                        
                        // Code points with rd=0 are hints
                    end
                end
                3'b100: begin
                    unique case (instr_i[11:10])
                        2'b00: begin // c.srli
                            alu_operation_o  = ALU_SRL;
                            alu_source_2_o   = ALU_SCR2_IMM;
                            immediate_type_o = IMM_CI;
                           
                            reg_alu_wen_o = 1'b1;
                           
                            rs1_addr_C = {2'b01, instr_i[9:7]};
                            rd_addr_C  = {2'b01, instr_i[9:7]};
                            
                            // For RV32C, shamt[5] must be zero
                            // The code points with shamt[5]=1 are designated for custom extensions
                            if (instr_i[12] == 1'b1)
                                illegal_instr_o = 1'b1;
                        end
                        2'b01: begin // c.srai
                            alu_operation_o  = ALU_SRA;
                            alu_source_2_o   = ALU_SCR2_IMM;
                            immediate_type_o = IMM_CI;
                           
                            reg_alu_wen_o = 1'b1;
                           
                            rs1_addr_C = {2'b01, instr_i[9:7]};
                            rd_addr_C  = {2'b01, instr_i[9:7]};
                            
                            // For RV32C, shamt[5] must be zero
                            // The code points with shamt[5]=1 are designated for custom extensions
                            if (instr_i[12] == 1'b1)
                                illegal_instr_o = 1'b1;
                        end
                        2'b10: begin // c.andi
                            alu_operation_o  = ALU_AND;
                            alu_source_2_o   = ALU_SCR2_IMM;
                            immediate_type_o = IMM_CI;
                           
                            reg_alu_wen_o = 1'b1;
                           
                            rs1_addr_C = {2'b01, instr_i[9:7]};
                            rd_addr_C  = {2'b01, instr_i[9:7]};
                        end
                        2'b11: begin
                            if (instr_i[12]) begin
                                illegal_instr_o = 1'b1;
                            end
                            else begin
                                unique case (instr_i[6:5])
                                    2'b00: begin // c.sub
                                        alu_operation_o = ALU_SUB;
                                        reg_alu_wen_o = 1'b1;
                                        rs1_addr_C = {2'b01, instr_i[9:7]};
                                        rs2_addr_C = {2'b01, instr_i[4:2]};
                                        rd_addr_C  = {2'b01, instr_i[9:7]};
                                    end
                                    2'b01: begin // c.xor
                                        alu_operation_o = ALU_XOR;
                                        reg_alu_wen_o = 1'b1;
                                        rs1_addr_C = {2'b01, instr_i[9:7]};
                                        rs2_addr_C = {2'b01, instr_i[4:2]};
                                        rd_addr_C  = {2'b01, instr_i[9:7]};
                                    end
                                    2'b10: begin // c.or
                                        alu_operation_o = ALU_OR;
                                        reg_alu_wen_o = 1'b1;
                                        rs1_addr_C = {2'b01, instr_i[9:7]};
                                        rs2_addr_C = {2'b01, instr_i[4:2]};
                                        rd_addr_C  = {2'b01, instr_i[9:7]};
                                    end
                                    2'b11: begin // c.and
                                        alu_operation_o = ALU_AND;
                                        reg_alu_wen_o = 1'b1;
                                        rs1_addr_C = {2'b01, instr_i[9:7]};
                                        rs2_addr_C = {2'b01, instr_i[4:2]};
                                        rd_addr_C  = {2'b01, instr_i[9:7]};
                                    end
                                    default: illegal_instr_o = 1'b1;
                                endcase
                            end
                        end
                        default: illegal_instr_o = 1'b1;
                    endcase
                end
                3'b101: begin // c.j
                    // ALU is unused
                    // The jump target has a dedicated adder in ID stage
                    alu_source_1_o   = ALU_SCR1_PC;
                    immediate_type_o = IMM_CJ;
            
                    pc_source_o  = PC_JAL;
                end
                3'b110: begin // c.beqz
                    // ALU does the comparison
                    // The branch target has a dedicated adder in ID stage
                    alu_operation_o  = ALU_SEQ;
                    immediate_type_o = IMM_CB;
            
                    pc_source_o = PC_BRANCH;
                    is_branch_o = 1'b1;
            
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = 5'd0;
                end
                3'b111: begin // c.bnez
                    // ALU does the comparison
                    // The branch target has a dedicated adder in ID stage
                    alu_operation_o  = ALU_SNE;
                    immediate_type_o = IMM_CB;
            
                    pc_source_o = PC_BRANCH;
                    is_branch_o = 1'b1;
                   
                    rs1_addr_C = {2'b01, instr_i[9:7]};
                    rs2_addr_C = 5'd0;
                end
                default: illegal_instr_o = 1'b1;
            endcase
        end

        OPCODE_RVC_2: begin
            case (funct3_C)
                3'b000: begin // c.slli
                    alu_operation_o = ALU_SLL;
                    alu_source_2_o  = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CI;
                    
                    reg_alu_wen_o   = 1'b1;
                    
                    // For RV32C, shamt[5] must be zero
                    // The code points with shamt[5]=1 are designated for custom extensions
                    if (instr_i[12] == 1'b1)
                        illegal_instr_o = 1'b1;
                end
                3'b010: begin // c.lwsp
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CSPL;
                    
                    reg_mem_wen_o    = 1'b1;

                    rs1_addr_C = 5'd2; // x2/sp
                    
                    // Code points with rd=0 are reserved
                    if (rd_addr_C == '0)
                        illegal_instr_o = 1'b1;
                end
                /*3'b011: begin // c.flwsp
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_I;
                    mem_data_type_o  = WORD;
                    //immediate_type_o = IMM_I;
                    reg_mem_wen_o    = 1'b1;
                    
                    immediate_type_o = IMM_CSPL;

                    rs1_addr_C = 5'd2; //x2
                    rd_addr_C  = instr_i[11:7];

                end*/
                3'b100: begin
                    if (funct4_C[0] == 1'd0) begin
                        if (rs2_addr_C == 5'd0) begin // c.jr
                            // ALU is unused
                            // The jump target has a dedicated adder in ID stage
                            alu_source_1_o   = ALU_SCR1_PC;
                            immediate_type_o = IMM_CJR;
                            
                            pc_source_o    = PC_JALR;
                            
                            // Code points with rs1=0 are reserved
                            if (rs1_addr_C == 5'd0)
                                illegal_instr_o = 1'b1;
                        end
                        else begin // c.mv
                            alu_operation_o = ALU_ADD;
                            alu_source_1_o  = ALU_SCR1_ZERO;
                            
                            reg_alu_wen_o   = 1'b1;
                            
                            // Code points with rd=0 are hints
                        end
                    end
                    else begin
                        if (rs2_addr_C == 5'd0) begin
                            if (rs1_addr_C == 5'd0) begin // c.ebreak
                                // NOT IMPLEMENTED!
                            end
                            else begin // c.jalr
                                // ALU calculates PC+2
                                // The jump target has a dedicated adder in ID stage
                                alu_operation_o  = ALU_ADD;
                                alu_source_1_o   = ALU_SCR1_PC;
                                alu_source_2_o   = ALU_SCR2_4_OR_2;
                                immediate_type_o = IMM_CJR;
                                
                                reg_alu_wen_o    = 1'b1;
                                pc_source_o      = PC_JALR;

                                rd_addr_C = 5'd1; // x1/ra
                            end
                        end
                        else begin // c.add
                            alu_operation_o = ALU_ADD;
                            reg_alu_wen_o   = 1'b1;
                            
                            // Code points with rd=0 are hints
                        end
                    end
                end
                3'b110: begin // c.swsp
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    immediate_type_o = IMM_CSPS;
                    
                    mem_wen_o        = 1'b1;

                    rs1_addr_C = 5'd2; // x2/sp
                end
                /*3'b111: begin // c.fswsp
                    alu_operation_o  = ALU_ADD;
                    alu_source_2_o   = ALU_SCR2_IMM;
                    mem_data_type_o  = WORD;
                    //immediate_type_o = IMM_S;
                    mem_wen_o        = 1'b1;

                    immediate_type_o = IMM_CSPS;

                    rs1_addr_C = 5'd2; //x2
                    rs2_addr_C = instr_i[6:2];
                end*/
                default: illegal_instr_o = 1'b1;
            endcase
        end
        
        default: illegal_instr_o = 1'b1;
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
            // ALU calculates PC+4
            // The jump target has a dedicated adder in ID stage
            alu_operation_o  = ALU_ADD;
            alu_source_1_o   = ALU_SCR1_PC;
            alu_source_2_o   = ALU_SCR2_4_OR_2;
            immediate_type_o = IMM_J;
            
            reg_alu_wen_o  = 1'b1;
            
            pc_source_o  = PC_JAL;
        end
        
        OPCODE_JALR: begin // jalr
            // ALU calculates PC+4
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
                    CSR_MCAUSE,
                    CSR_MSCRATCH: ;
                    
                    // Floating point
                    CSR_FFLAGS: 
                        if(!ISA_F /*|| fs_off_i*/) illegal_instr_o = 1'b1;
                    CSR_FRM,
                    CSR_FCSR:
                        if(!ISA_F /*|| fs_off_i*/) begin
                            illegal_instr_o = 1'b1;
                        end
                        else begin
                            if(csr_op_o != CSR_READ) csr_status_o = 1'b1;
                        end
                     

                    default: illegal_instr_o = 1'b1;
                endcase
            end
        end
        
        /////////////////////////////////////////////
        /////////////       FPU         /////////////
        /////////////////////////////////////////////
        // TODO: raise illegal instruction for invalid rounding mode??
        OPCODE_OP_FP:begin
            if (ISA_F) begin
                fpu_req_o = 1'b1;
                reg_alu_wen_o = 1'b1;
                rs1_src_bank_o = F_REG;
                rs2_src_bank_o = F_REG;
                rs3_src_bank_o = F_REG;
                rd_dst_bank_o  = F_REG;
                alu_result_mux_o = FPU_RESULT;
                unique case (funct7)
                    7'b000_0000: begin // fadd.s
                        fpu_op_o = fpnew_pkg::ADD;
                    end
                    7'b000_0100: begin // fsub.s
                        fpu_op_o = fpnew_pkg::ADD;
                        fpu_op_mod_o = 1'b1;
                    end
                    7'b000_1000: begin // fmul.s
                        fpu_op_o = fpnew_pkg::MUL;
                    end
                    7'b000_1100: begin // fdiv.s
                        fpu_op_o = fpnew_pkg::DIV;
                    end
                    7'b010_1100: begin // fsqrt.s
                        fpu_op_o = fpnew_pkg::SQRT;
                        if (instr_i[24:20] != 5'b0) illegal_instr_o = 1'b1;
                    end
                    7'b001_0000: begin
                        fpu_op_o = fpnew_pkg::SGNJ;
                        unique case (funct3)
                            3'b000:begin // fsgnj.s
                                fpu_rnd_mode_o = fpnew_pkg::RNE;
                            end
                            3'b001:begin // fsgnjn.s
                                fpu_rnd_mode_o = fpnew_pkg::RTZ;
                            end
                            3'b010:begin // fsgnjx.s
                                fpu_rnd_mode_o = fpnew_pkg::RDN;
                            end
                            default: illegal_instr_o = 1'b1;
                    endcase
                    end
                    7'b001_0100: begin
                        fpu_op_o = fpnew_pkg::MINMAX;
                        unique case (funct3)
                            3'b000: begin // fmin.s
                                fpu_rnd_mode_o = fpnew_pkg::RNE;
                            end
                            3'b001: begin // fmax.s
                                fpu_rnd_mode_o = fpnew_pkg::RTZ;
                            end
                            default: illegal_instr_o = 1'b1;
                        endcase
                    end
                    7'b110_0000: begin
                        fpu_op_o = fpnew_pkg::F2I;
                        rd_dst_bank_o  = X_REG;
                        unique case (instr_i[24:20])
                            5'b00000: begin // fcvt.w.s
                                fpu_op_mod_o = 1'b0;
                            end
                            5'b00001: begin // fcvt.wu.s
                                fpu_op_mod_o = 1'b1;
                            end
                            default: illegal_instr_o = 1'b1;
                        endcase
                    end
                    7'b110_1000: begin
                        fpu_op_o = fpnew_pkg::I2F;
                        rs1_src_bank_o = X_REG;
                        unique case (instr_i[24:20])
                            5'b00000: begin // fcvt.s.w
                                fpu_op_mod_o = 1'b0;
                            end
                            5'b00001: begin // fcvt.s.wu
                                fpu_op_mod_o = 1'b1;
                            end
                            default: illegal_instr_o = 1'b1;
                        endcase
                    end
                    7'b101_0000: begin
                        fpu_op_o = fpnew_pkg::CMP;
                        rd_dst_bank_o = X_REG;
                        unique case (funct3)
                            3'b000: begin // fle.s
                                fpu_rnd_mode_o = fpnew_pkg::RNE;
                            end
                            3'b001: begin // flt.s
                                fpu_rnd_mode_o = fpnew_pkg::RTZ;
                            end
                            3'b010: begin // feq.s
                                fpu_rnd_mode_o = fpnew_pkg::RDN;
                            end
                            default: illegal_instr_o = 1'b1;
                        endcase
                    end
                    7'b111_0000: begin
                        if(instr_i[24:20] != 5'b0) illegal_instr_o = 1'b1;
                        rd_dst_bank_o = X_REG;
                        unique case (funct3)
                            3'b000: begin // fmv.x.w
                                // Move from F reg to X reg
                                // TODO: test fpu_req_o = 1'b0;
                                fpu_op_o = fpnew_pkg::SGNJ;
                                fpu_op_mod_o = 1'b1;
                                fpu_rnd_mode_o = fpnew_pkg::RUP;
                            end
                            3'b001: begin // fclass.s
                                fpu_op_o = fpnew_pkg::CLASSIFY;
                                fpu_rnd_mode_o = fpnew_pkg::RNE; // TODO: is this necessary?
                            end
                            default: illegal_instr_o = 1'b1;
                        endcase
                    end
                    7'b111_1000: begin // fmv.w.x
                        // Move from X reg to F reg
                        // TODO: test fpu_req_o = 1'b0;
                        fpu_op_o = fpnew_pkg::SGNJ;
                        fpu_op_mod_o = 1'b0;
                        fpu_rnd_mode_o = 3'b011;
                        rs1_src_bank_o = X_REG;
                        
                        if(instr_i[24:20] != 5'b0) illegal_instr_o = 1'b1;
                        if(funct3         != 3'b0) illegal_instr_o = 1'b1;
                    end
                    default: illegal_instr_o = 1'b1;
            
                endcase
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_FMADD_FP: begin // fmadd.s
            if (ISA_F) begin
                fpu_req_o = 1'b1;
                reg_alu_wen_o = 1'b1;
                rs1_src_bank_o = F_REG;
                rs2_src_bank_o = F_REG;
                rs3_src_bank_o = F_REG;
                rd_dst_bank_o  = X_REG;
                rs3_is_used_o = 1'b1;
                fpu_op_o = fpnew_pkg::FMADD;
                alu_result_mux_o = FPU_RESULT;
                
                if(instr_i[26:25] != 2'b0) illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_FMSUB_FP: begin // fmsub.s
            if (ISA_F) begin
                fpu_req_o = 1'b1;
                reg_alu_wen_o = 1'b1;
                rs1_src_bank_o = F_REG;
                rs2_src_bank_o = F_REG;
                rs3_src_bank_o = F_REG;
                rd_dst_bank_o  = X_REG;
                rs3_is_used_o = 1'b1;
                fpu_op_o = fpnew_pkg::FMADD;
                fpu_op_mod_o = 1'b1;
                alu_result_mux_o = FPU_RESULT;
                
                if(instr_i[26:25] != 2'b0) illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_FNMSUB_FP: begin // fnmsub.s
            if (ISA_F) begin
                fpu_req_o = 1'b1;
                reg_alu_wen_o = 1'b1;
                rs1_src_bank_o = F_REG;
                rs2_src_bank_o = F_REG;
                rs3_src_bank_o = F_REG;
                rd_dst_bank_o  = X_REG;
                rs3_is_used_o = 1'b1;
                fpu_op_o = fpnew_pkg::FNMSUB;
                alu_result_mux_o = FPU_RESULT;
                
                if(instr_i[26:25] != 2'b0) illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_FNMADD_FP: begin // fnmadd.s
            if (ISA_F) begin
                fpu_req_o = 1'b1;
                reg_alu_wen_o = 1'b1;
                rs1_src_bank_o = F_REG;
                rs2_src_bank_o = F_REG;
                rs3_src_bank_o = F_REG;
                rd_dst_bank_o  = X_REG;
                rs3_is_used_o = 1'b1;
                fpu_op_o = fpnew_pkg::FNMSUB;
                fpu_op_mod_o = 1'b1;
                alu_result_mux_o = FPU_RESULT;
                
                if(instr_i[26:25] != 2'b0) illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_STORE_FP: begin // fsw
            if (ISA_F) begin
                reg_alu_wen_o = 1'b0;
                // is_immediate_F = 1'b1;
                fpu_op_o = ALU_ADD;
                
                alu_source_2_o   = ALU_SCR2_IMM;
                immediate_type_o = IMM_S;
                mem_data_type_o = WORD;
                mem_wen_o = 1'b1;
                rs2_src_bank_o = F_REG;
                
                if(funct3 != 3'b010) 
                    illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        OPCODE_LOAD_FP: begin // flw
            if (ISA_F) begin
                reg_alu_wen_o = 1'b1;
                // is_immediate_F = 1'b1;
                fpu_op_o = ALU_ADD;

                alu_source_2_o   = ALU_SCR2_IMM;
                immediate_type_o = IMM_I;
                mem_data_type_o = WORD;
                reg_mem_wen_o = 1'b1;
                rd_dst_bank_o = F_REG;
                
                if(funct3 != 3'b010) 
                    illegal_instr_o = 1'b1;
            end 
            else begin 
                illegal_instr_o = 1'b1;
            end
        end
        
        default: illegal_instr_o = 1'b1;
    endcase
    end
end

`ifdef JASPER
`default_nettype wire
`endif
    
endmodule
