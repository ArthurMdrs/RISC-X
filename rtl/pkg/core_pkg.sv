package core_pkg;

// ALU-related types

typedef enum logic [3:0] {
    ALU_AND,    // 0000
    ALU_OR,     // 0001
    ALU_XOR,    // 0010
    
    ALU_ADD,    // 0011
    ALU_SUB,    // 0100
    
    ALU_SLL,    // 0101
    ALU_SRL,    // 0110
    ALU_SRA,    // 0111
    
    ALU_SLT,    // 1000
    ALU_SLTU,   // 1001
    ALU_SGE,    // 1010
    ALU_SGEU,   // 1011
    ALU_SEQ,    // 1100
    ALU_SNE     // 1101
} alu_operation_t;

typedef enum logic [1:0] { 
    ALU_SCR1_RS1,
    ALU_SCR1_PC,
    ALU_SCR1_ZERO,
    ALU_SCR1_IMM_CSR
} alu_source_1_t;

typedef enum logic [1:0] { 
    ALU_SCR2_RS2,
    ALU_SCR2_IMM,
    ALU_SCR2_4_OR_2 // Used to calculate PC + 4 or PC + 2
} alu_source_2_t;



typedef enum logic [4:0] {
    IMM_I,
    IMM_S,
    IMM_B,
    IMM_U,
    IMM_J,

    IMM_CJ,
    IMM_CJR,
    IMM_CI,
    IMM_CLUI,
    IMM_CSPL,
    IMM_CSPS,
    IMM_CLS,
    IMM_CB
} immediate_source_t;

// PC-related types

typedef enum logic [1:0] {
    PC_P_4,
    PC_JAL,
    PC_JALR,
    PC_BRANCH
} pc_source_t;

// Memory-access-related types

typedef enum logic [1:0] {
    BYTE,
    HALF_WORD,
    WORD
} data_type_t;

// Forwarding-related types

typedef enum logic [2:0] {
    NO_FORWARD,
    FWD_EX_ALU_RES_TO_ID,
    FWD_MEM_ALU_RES_TO_ID,
    FWD_MEM_RDATA_TO_ID,
    FWD_WB_ALU_RES_TO_ID,
    FWD_WB_RDATA_TO_ID
} forward_t;

// CSR-related types

typedef enum logic [1:0] {
    CSR_READ,
    CSR_WRITE,
    CSR_SET,
    CSR_CLEAR
} csr_operation_t;

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
localparam logic [6:0] OPCODE_SYSTEM = 7'b111_0011; // 7'h73

// Type RVC opcode:

localparam logic [6:0] OPCODE_RVC_1 = 7'bxxx_xx00; // First Quadrant
localparam logic [6:0] OPCODE_RVC_2 = 7'bxxx_xx01; // Second
localparam logic [6:0] OPCODE_RVC_3 = 7'bxxx_xx10; // Third

// CSRs mnemonics (some might not be implemented)

typedef enum logic [11:0] {
    ///////////////////////////////////////////////////////
    // User CSRs
    ///////////////////////////////////////////////////////

    // User trap setup
    CSR_USTATUS = 12'h000,  // 

    // Floating Point
    CSR_FFLAGS = 12'h001,  // 
    CSR_FRM    = 12'h002,  // 
    CSR_FCSR   = 12'h003,  // 

    // User trap setup
    CSR_UTVEC = 12'h005,  // 

    // User trap handling
    CSR_UEPC   = 12'h041,  // 
    CSR_UCAUSE = 12'h042,  // 

    ///////////////////////////////////////////////////////
    // User Custom CSRs
    ///////////////////////////////////////////////////////

    // Privilege
    CSR_PRIVLV = 12'hCD1,  // Custom CSR. Privilege Level

    ///////////////////////////////////////////////////////
    // Machine CSRs
    ///////////////////////////////////////////////////////

    // Machine trap setup
    CSR_MSTATUS = 12'h300,
    CSR_MISA    = 12'h301,
    CSR_MIE     = 12'h304,
    CSR_MTVEC   = 12'h305,

    // Performance counters
    CSR_MCOUNTEREN    = 12'h306,
    CSR_MCOUNTINHIBIT = 12'h320,
    CSR_MHPMEVENT3    = 12'h323,
    CSR_MHPMEVENT4    = 12'h324,
    CSR_MHPMEVENT5    = 12'h325,
    CSR_MHPMEVENT6    = 12'h326,
    CSR_MHPMEVENT7    = 12'h327,
    CSR_MHPMEVENT8    = 12'h328,
    CSR_MHPMEVENT9    = 12'h329,
    CSR_MHPMEVENT10   = 12'h32A,
    CSR_MHPMEVENT11   = 12'h32B,
    CSR_MHPMEVENT12   = 12'h32C,
    CSR_MHPMEVENT13   = 12'h32D,
    CSR_MHPMEVENT14   = 12'h32E,
    CSR_MHPMEVENT15   = 12'h32F,
    CSR_MHPMEVENT16   = 12'h330,
    CSR_MHPMEVENT17   = 12'h331,
    CSR_MHPMEVENT18   = 12'h332,
    CSR_MHPMEVENT19   = 12'h333,
    CSR_MHPMEVENT20   = 12'h334,
    CSR_MHPMEVENT21   = 12'h335,
    CSR_MHPMEVENT22   = 12'h336,
    CSR_MHPMEVENT23   = 12'h337,
    CSR_MHPMEVENT24   = 12'h338,
    CSR_MHPMEVENT25   = 12'h339,
    CSR_MHPMEVENT26   = 12'h33A,
    CSR_MHPMEVENT27   = 12'h33B,
    CSR_MHPMEVENT28   = 12'h33C,
    CSR_MHPMEVENT29   = 12'h33D,
    CSR_MHPMEVENT30   = 12'h33E,
    CSR_MHPMEVENT31   = 12'h33F,

    // Machine trap handling
    CSR_MSCRATCH = 12'h340,
    CSR_MEPC     = 12'h341,
    CSR_MCAUSE   = 12'h342,
    CSR_MTVAL    = 12'h343,
    CSR_MIP      = 12'h344,

    // Physical memory protection (PMP)
    CSR_PMPCFG0   = 12'h3A0,  // 
    CSR_PMPCFG1   = 12'h3A1,  // 
    CSR_PMPCFG2   = 12'h3A2,  // 
    CSR_PMPCFG3   = 12'h3A3,  // 
    CSR_PMPADDR0  = 12'h3B0,  // 
    CSR_PMPADDR1  = 12'h3B1,  // 
    CSR_PMPADDR2  = 12'h3B2,  // 
    CSR_PMPADDR3  = 12'h3B3,  // 
    CSR_PMPADDR4  = 12'h3B4,  // 
    CSR_PMPADDR5  = 12'h3B5,  // 
    CSR_PMPADDR6  = 12'h3B6,  // 
    CSR_PMPADDR7  = 12'h3B7,  // 
    CSR_PMPADDR8  = 12'h3B8,  // 
    CSR_PMPADDR9  = 12'h3B9,  // 
    CSR_PMPADDR10 = 12'h3BA,  // 
    CSR_PMPADDR11 = 12'h3BB,  // 
    CSR_PMPADDR12 = 12'h3BC,  // 
    CSR_PMPADDR13 = 12'h3BD,  // 
    CSR_PMPADDR14 = 12'h3BE,  // 
    CSR_PMPADDR15 = 12'h3BF,  // 

    // Trigger
    CSR_TSELECT  = 12'h7A0,
    CSR_TDATA1   = 12'h7A1,
    CSR_TDATA2   = 12'h7A2,
    CSR_TDATA3   = 12'h7A3,
    CSR_TINFO    = 12'h7A4,
    CSR_MCONTEXT = 12'h7A8,
    CSR_SCONTEXT = 12'h7AA,

    // Debug/trace
    CSR_DCSR = 12'h7B0,
    CSR_DPC  = 12'h7B1,

    // Debug
    CSR_DSCRATCH0 = 12'h7B2,
    CSR_DSCRATCH1 = 12'h7B3,

    // Hardware Performance Monitor
    CSR_MCYCLE        = 12'hB00,
    CSR_MINSTRET      = 12'hB02,
    CSR_MHPMCOUNTER3  = 12'hB03,
    CSR_MHPMCOUNTER4  = 12'hB04,
    CSR_MHPMCOUNTER5  = 12'hB05,
    CSR_MHPMCOUNTER6  = 12'hB06,
    CSR_MHPMCOUNTER7  = 12'hB07,
    CSR_MHPMCOUNTER8  = 12'hB08,
    CSR_MHPMCOUNTER9  = 12'hB09,
    CSR_MHPMCOUNTER10 = 12'hB0A,
    CSR_MHPMCOUNTER11 = 12'hB0B,
    CSR_MHPMCOUNTER12 = 12'hB0C,
    CSR_MHPMCOUNTER13 = 12'hB0D,
    CSR_MHPMCOUNTER14 = 12'hB0E,
    CSR_MHPMCOUNTER15 = 12'hB0F,
    CSR_MHPMCOUNTER16 = 12'hB10,
    CSR_MHPMCOUNTER17 = 12'hB11,
    CSR_MHPMCOUNTER18 = 12'hB12,
    CSR_MHPMCOUNTER19 = 12'hB13,
    CSR_MHPMCOUNTER20 = 12'hB14,
    CSR_MHPMCOUNTER21 = 12'hB15,
    CSR_MHPMCOUNTER22 = 12'hB16,
    CSR_MHPMCOUNTER23 = 12'hB17,
    CSR_MHPMCOUNTER24 = 12'hB18,
    CSR_MHPMCOUNTER25 = 12'hB19,
    CSR_MHPMCOUNTER26 = 12'hB1A,
    CSR_MHPMCOUNTER27 = 12'hB1B,
    CSR_MHPMCOUNTER28 = 12'hB1C,
    CSR_MHPMCOUNTER29 = 12'hB1D,
    CSR_MHPMCOUNTER30 = 12'hB1E,
    CSR_MHPMCOUNTER31 = 12'hB1F,

    CSR_MCYCLEH        = 12'hB80,
    CSR_MINSTRETH      = 12'hB82,
    CSR_MHPMCOUNTER3H  = 12'hB83,
    CSR_MHPMCOUNTER4H  = 12'hB84,
    CSR_MHPMCOUNTER5H  = 12'hB85,
    CSR_MHPMCOUNTER6H  = 12'hB86,
    CSR_MHPMCOUNTER7H  = 12'hB87,
    CSR_MHPMCOUNTER8H  = 12'hB88,
    CSR_MHPMCOUNTER9H  = 12'hB89,
    CSR_MHPMCOUNTER10H = 12'hB8A,
    CSR_MHPMCOUNTER11H = 12'hB8B,
    CSR_MHPMCOUNTER12H = 12'hB8C,
    CSR_MHPMCOUNTER13H = 12'hB8D,
    CSR_MHPMCOUNTER14H = 12'hB8E,
    CSR_MHPMCOUNTER15H = 12'hB8F,
    CSR_MHPMCOUNTER16H = 12'hB90,
    CSR_MHPMCOUNTER17H = 12'hB91,
    CSR_MHPMCOUNTER18H = 12'hB92,
    CSR_MHPMCOUNTER19H = 12'hB93,
    CSR_MHPMCOUNTER20H = 12'hB94,
    CSR_MHPMCOUNTER21H = 12'hB95,
    CSR_MHPMCOUNTER22H = 12'hB96,
    CSR_MHPMCOUNTER23H = 12'hB97,
    CSR_MHPMCOUNTER24H = 12'hB98,
    CSR_MHPMCOUNTER25H = 12'hB99,
    CSR_MHPMCOUNTER26H = 12'hB9A,
    CSR_MHPMCOUNTER27H = 12'hB9B,
    CSR_MHPMCOUNTER28H = 12'hB9C,
    CSR_MHPMCOUNTER29H = 12'hB9D,
    CSR_MHPMCOUNTER30H = 12'hB9E,
    CSR_MHPMCOUNTER31H = 12'hB9F,

    CSR_CYCLE        = 12'hC00,
    CSR_INSTRET      = 12'hC02,
    CSR_HPMCOUNTER3  = 12'hC03,
    CSR_HPMCOUNTER4  = 12'hC04,
    CSR_HPMCOUNTER5  = 12'hC05,
    CSR_HPMCOUNTER6  = 12'hC06,
    CSR_HPMCOUNTER7  = 12'hC07,
    CSR_HPMCOUNTER8  = 12'hC08,
    CSR_HPMCOUNTER9  = 12'hC09,
    CSR_HPMCOUNTER10 = 12'hC0A,
    CSR_HPMCOUNTER11 = 12'hC0B,
    CSR_HPMCOUNTER12 = 12'hC0C,
    CSR_HPMCOUNTER13 = 12'hC0D,
    CSR_HPMCOUNTER14 = 12'hC0E,
    CSR_HPMCOUNTER15 = 12'hC0F,
    CSR_HPMCOUNTER16 = 12'hC10,
    CSR_HPMCOUNTER17 = 12'hC11,
    CSR_HPMCOUNTER18 = 12'hC12,
    CSR_HPMCOUNTER19 = 12'hC13,
    CSR_HPMCOUNTER20 = 12'hC14,
    CSR_HPMCOUNTER21 = 12'hC15,
    CSR_HPMCOUNTER22 = 12'hC16,
    CSR_HPMCOUNTER23 = 12'hC17,
    CSR_HPMCOUNTER24 = 12'hC18,
    CSR_HPMCOUNTER25 = 12'hC19,
    CSR_HPMCOUNTER26 = 12'hC1A,
    CSR_HPMCOUNTER27 = 12'hC1B,
    CSR_HPMCOUNTER28 = 12'hC1C,
    CSR_HPMCOUNTER29 = 12'hC1D,
    CSR_HPMCOUNTER30 = 12'hC1E,
    CSR_HPMCOUNTER31 = 12'hC1F,

    CSR_CYCLEH        = 12'hC80,
    CSR_INSTRETH      = 12'hC82,
    CSR_HPMCOUNTER3H  = 12'hC83,
    CSR_HPMCOUNTER4H  = 12'hC84,
    CSR_HPMCOUNTER5H  = 12'hC85,
    CSR_HPMCOUNTER6H  = 12'hC86,
    CSR_HPMCOUNTER7H  = 12'hC87,
    CSR_HPMCOUNTER8H  = 12'hC88,
    CSR_HPMCOUNTER9H  = 12'hC89,
    CSR_HPMCOUNTER10H = 12'hC8A,
    CSR_HPMCOUNTER11H = 12'hC8B,
    CSR_HPMCOUNTER12H = 12'hC8C,
    CSR_HPMCOUNTER13H = 12'hC8D,
    CSR_HPMCOUNTER14H = 12'hC8E,
    CSR_HPMCOUNTER15H = 12'hC8F,
    CSR_HPMCOUNTER16H = 12'hC90,
    CSR_HPMCOUNTER17H = 12'hC91,
    CSR_HPMCOUNTER18H = 12'hC92,
    CSR_HPMCOUNTER19H = 12'hC93,
    CSR_HPMCOUNTER20H = 12'hC94,
    CSR_HPMCOUNTER21H = 12'hC95,
    CSR_HPMCOUNTER22H = 12'hC96,
    CSR_HPMCOUNTER23H = 12'hC97,
    CSR_HPMCOUNTER24H = 12'hC98,
    CSR_HPMCOUNTER25H = 12'hC99,
    CSR_HPMCOUNTER26H = 12'hC9A,
    CSR_HPMCOUNTER27H = 12'hC9B,
    CSR_HPMCOUNTER28H = 12'hC9C,
    CSR_HPMCOUNTER29H = 12'hC9D,
    CSR_HPMCOUNTER30H = 12'hC9E,
    CSR_HPMCOUNTER31H = 12'hC9F,

    // Machine information
    CSR_MVENDORID = 12'hF11,
    CSR_MARCHID   = 12'hF12,
    CSR_MIMPID    = 12'hF13,
    CSR_MHARTID   = 12'hF14
} csr_addr_t;

// Typedef for mstatus CSR

typedef struct packed {
    logic uie;
    logic sie;
    logic hie;
    logic mie;
    logic upie;
    logic spie;
    logic hpie;
    logic mpie;
    logic spp;
    logic [1:0] hpp;
    logic [1:0] mpp;
    logic mprv;
} Status_t;

endpackage 