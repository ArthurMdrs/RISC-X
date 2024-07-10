package core_pkg;

typedef enum logic [3:0] {
    ALU_AND, 
    ALU_OR, 
    ALU_XOR, 
    
    ALU_ADD, 
    ALU_SUB, 
    
    ALU_SLL, 
    ALU_SRL, 
    ALU_SRA,
    
    ALU_SLT, 
    ALU_SLTU, 
    ALU_SGE, 
    ALU_SGEU,
    ALU_SEQ,
    ALU_SNE
} alu_operation_t;

typedef enum logic [1:0] { 
    ALU_SCR1_RS1,
    ALU_SCR1_PC,
    ALU_SCR1_ZERO
} alu_source_1_t;

typedef enum logic [1:0] { 
    ALU_SCR2_RS2,
    ALU_SCR2_IMM,
    ALU_SCR2_4_OR_2 // Used to calculate PC + 4 or PC + 2
} alu_source_2_t;



typedef enum logic [2:0] {
    IMM_I,
    IMM_S,
    IMM_B,
    IMM_U,
    IMM_J
} immediate_source_t;



typedef enum logic [1:0] {
    PC_P_4,
    PC_JAL,
    PC_JALR,
    PC_BRANCH
} pc_source_t;

// typedef enum logic [2:0] {
//     BRANCH_EQ,
//     BRANCH_NE,
//     BRANCH_BLT,
//     BRANCH_BGE,
//     BRANCH_NONE
// } branch_type_t;



typedef enum logic [1:0] {
    BYTE,
    HALF_WORD,
    WORD
} data_type_t;



typedef enum logic [2:0] {
    NO_FORWARD,
    // FWD_MEM_TO_EX,
    // FWD_WB_TO_EX
    FWD_EX_TO_ID,
    // FWD_MEM_TO_ID
    FWD_MEM_ALU_RES_TO_ID,
    FWD_MEM_RDATA_TO_ID,
    FWD_WB_ALU_RES_TO_ID,
    FWD_WB_RDATA_TO_ID
} forward_t;



// OpCodes
localparam logic [6:0] OPCODE_OP     = 7'b011_0011; // 7'h33
localparam logic [6:0] OPCODE_OP_IMM = 7'b001_0011; // 7'h13
localparam logic [6:0] OPCODE_LOAD   = 7'b000_0011; // 7'h03
localparam logic [6:0] OPCODE_STORE  = 7'b010_0011; // 7'h23
localparam logic [6:0] OPCODE_BRANCH = 7'b110_0011; // 7'h63
localparam logic [6:0] OPCODE_JAL    = 7'b110_1111; // 7'h6f
localparam logic [6:0] OPCODE_JALR   = 7'b110_0111; // 7'h67
localparam logic [6:0] OPCODE_LUI    = 7'b011_0111; // 7'h37
localparam logic [6:0] OPCODE_AUIPC  = 7'b001_0111; // 7'h17

endpackage 