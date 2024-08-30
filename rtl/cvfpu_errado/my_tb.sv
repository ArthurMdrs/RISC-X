module my_tb ();


import fpnew_pkg::*;

// Parameters below are configurable in CV32
localparam FPU_ADDMUL_LAT = 5; // Floating-Point ADDition/MULtiplication pipeline registers number
localparam FPU_OTHERS_LAT = 3; // Floating-Point COMParison/CONVersion pipeline registers number

// Parameters below are NOT configurable in CV32, defined in a pkg
localparam C_LAT_DIVSQRT = 1;
localparam APU_NARGS_CPU = 3;
localparam APU_NUSFLAGS_CPU = 5;


// -----------
// FPU Config
// -----------

// Features (enabled formats, vectors etc.)
localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
    Width: 32, // Width of the datapath and of the input/output data ports
    EnableVectors: 0, // If set to 1, vectorial execution units will be generated
    EnableNanBox: 0, // Controls whether input value NaN-boxing is enforced
    FpFmtMask: {// FP32, FP64, FP16,  FP8, FP16alt  // If a bit is set, hardware for the corresponding float format is generated
                   1'b1, 1'b0, 1'b0, 1'b0, 1'b0 
               },
    IntFmtMask: {// INT8, INT16, INT32, INT64 // If a bit is set, hardware for the corresponding int format is generated
                    1'b0,  1'b0,  1'b1,  1'b0
                }
};

// Implementation (number of registers etc)
localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
    // Sets a number of pipeline stages to be inserted into the units per operation group for each format
    // Operation groups: ADDMUL, DIVSQRT, NONCOMP, CONV
    // Formats: FP32, FP64, FP16, FP8, FP16alt
    PipeRegs: '{
        '{default: FPU_ADDMUL_LAT}, // ADDMUL
        '{default: C_LAT_DIVSQRT},  // DIVSQRT
        '{default: FPU_OTHERS_LAT}, // NONCOMP
        '{default: FPU_OTHERS_LAT}  // CONV
    },
    // Sets the unit types for the units per operation group for each format
    // Unit types: DISABLED, PARALLEL, MERGED
    UnitTypes: '{
        '{default: fpnew_pkg::MERGED},   // ADDMUL
        '{default: fpnew_pkg::MERGED},   // DIVSQRT
        '{default: fpnew_pkg::PARALLEL}, // NONCOMP
        '{default: fpnew_pkg::MERGED}    // CONV
    },
    PipeConfig: fpnew_pkg::AFTER
};

// Select the division/square root unit
localparam fpnew_pkg::divsqrt_unit_t DIV_SQRT_SEL = TH32;

// Parameters used in vectorial operations (NOT SUPPORTED)
localparam TRUE_SIMD_CLASS  = 0;
localparam ENABLE_SIMD_MASK = 0;

//---------------
// Decoder ports
//---------------

logic [31:0] inst;
logic [2:0] roundmode_wire;
logic fpu_op_mod_wire;
logic rs1_isF_wire;
logic rs2_isF_wire;
logic rd_isF_wire;
logic rs3_is_used_wire;
logic [4:0] rs3_addr_F_wire;
logic [4:0] is_store_wire;
logic [3:0] fpu_op_wire;

//---------------
// Decoder instance
//---------------

decoder decoder(
    .instr_i(inst), // Entrada
    .is_compressed_i(0), // Entrada
    .roundmode_o(roundmode_wire), // Foi
    .fpu_op_mod_o(fpu_op_mod_wire), // Foi
    .rs1_isF_o(rs1_isF_wire), // Não usa
    .rs2_isF_o(rs2_isF_wire), // Não usa
    .rd_isF_o(rd_isF_wire), // Não usa
    .rs3_is_used_o(rs3_is_used_wire), // Não usa
    .fpu_op_o(fpu_op_wire), // Foi
    .rs3_addr_F_o(rs3_addr_F_wire)); // Não usa

//---------------
// FPU ports
//---------------

// Clock and Reset
logic clk_i;
logic rst_ni;

// APU Side: Master port
logic apu_req_i; // Handshake signal
logic apu_gnt_o; // Handshake signal

// request channel
logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_i; // [2:0][31:0] -> 3 operands

fpnew_pkg::operation_e fpu_op;      // Operation to be performed
logic                  fpu_op_mod;  // Operation modifier (example: add becomes sub)
logic                  fpu_vec_op;  // Indicates vectorial operation (NOT SUPPORTED)

fpnew_pkg::fp_format_e  fpu_dst_fmt; // Float format of destination (result) (FP32, FP64, FP16, FP8, FP16alt)
fpnew_pkg::fp_format_e  fpu_src_fmt; // Float format of source operands (FP32, FP64, FP16, FP8, FP16alt)
fpnew_pkg::int_format_e fpu_int_fmt; // Integer format (INT8, INT16, INT32, INT64)
fpnew_pkg::roundmode_e  fp_rnd_mode; // Rounding mode (RNE, RTZ, RDN, RUP, RMM, ROD, DYN)

// response channel
logic                        apu_rvalid_o; // Handshake signal
logic [                31:0] apu_rdata_o;  // Operation result
logic [APU_NUSFLAGS_CPU-1:0] apu_rflags_o; // Flags for the fflags CSR (NV, DZ, OF, UF, NX)


//---------------
// FPU instance
//---------------

fpnew_top #(
    .Features       (FPU_FEATURES),
    .Implementation (FPU_IMPLEMENTATION),
    .DivSqrtSel     (DIV_SQRT_SEL),
    .TagType        (logic),
    .TrueSIMDClass  (TRUE_SIMD_CLASS),
    .EnableSIMDMask (ENABLE_SIMD_MASK)
) fpu_inst (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    // Input signals
    .operands_i     (apu_operands_i),
    .rnd_mode_i     (roundmode_wire), // Decoder
    .op_i           (fpu_op_wire), // Decoder
    .op_mod_i       (fpu_op_mod_wire), // Decoder
    .src_fmt_i      (fpu_src_fmt),
    .dst_fmt_i      (fpu_dst_fmt),
    .int_fmt_i      (fpu_int_fmt),
    .vectorial_op_i (fpu_vec_op),
    .tag_i          (1'b0),
    .simd_mask_i    (1'b0), // used in vectorial operations (NOT SUPPORTED)
    // Input Handshake
    .in_valid_i     (apu_req_i),
    .in_ready_o     (apu_gnt_o),
    .flush_i        (1'b0),
    // Output signals
    .result_o       (apu_rdata_o),
    .status_o       (apu_rflags_o), // exception flags for the fflags CSR (NV, DZ, OF, UF, NX) 
    .tag_o          (  /* unused */),
    // Output handshake
    .out_valid_o    (apu_rvalid_o),
    .out_ready_i    (1'b1),
    // Indication of valid data in flight
    .busy_o         (  /* unused */)
);


//-------------
// Assignments
//-------------

// Vectorial operations are not supported
assign fpu_vec_op = 1'b0;

// Set the operation to multiplication, for now
// assign fpu_op = ADDS;

// Select the operation modifier
// assign fpu_op_mod = 1'b0;

// Select formats
assign fpu_int_fmt = INT32; // We only have 32-bit integers
assign fpu_src_fmt = FP32;  // We only support single-precision floats
assign fpu_dst_fmt = FP32;  // We only support single-precision floats

// Select rounding mode
// assign fp_rnd_mode = RNE;


//---------------------
// Simulation
//---------------------

// Use variable below to get FP representation of result
real res_fp;

// Generate clock
initial begin
    clk_i = 0;
    repeat (10_000)
        #1 clk_i = !clk_i;
    $finish;
end

logic [31:0] num_a[0:9] = {
    32'h4091EB85, // 4.56 em IEEE-754
    32'h402CCCCD, // 2.71 em IEEE-754
    32'hBF9D70A4, // -1.23 em IEEE-754
    32'h411FD70A, // 9.99 em IEEE-754
    32'h40FCA3D7, // 7.89 em IEEE-754
    32'hC0D90FDB, // -6.78 em IEEE-754
    32'h4091EB85, // 4.56 em IEEE-754
    32'hC1133333, // -8.90 em IEEE-754
    32'h3DF5C28F, // 0.12 em IEEE-754
    32'hC0B55555  // -5.67 em IEEE-754
};

logic [31:0] num_b[0:9] = {
    32'hC048F5C3, // -3.14 em IEEE-754
    32'hC0AD70A4, // -4.32 em IEEE-754
    32'h406E6666, // 3.45 em IEEE-754
    32'hC1C7C28F, // -9.87 em IEEE-754
    32'h40D147AE, // 6.54 em IEEE-754
    32'hC01D70A4, // -2.34 em IEEE-754
    32'h40F5C28F, // 7.65 em IEEE-754
    32'hBF9D70A4, // -1.23 em IEEE-754
    32'h4110A3D7, // 8.76 em IEEE-754
    32'hC0A3D70A  // -3.21 em IEEE-754
};

logic [31:0] num_c[0:9] = {
    32'h3F81EB85, // 1.01 em IEEE-754
    32'hC0D90FDB, // -6.78 em IEEE-754
    32'h401D70A4, // 2.34 em IEEE-754
    32'hC1133333, // -8.90 em IEEE-754
    32'h4112D70A, // 9.12 em IEEE-754
    32'hC0A3D70A, // -3.21 em IEEE-754
    32'h3F81EB85, // 1.01 em IEEE-754
    32'hC0F5C28F, // -7.65 em IEEE-754
    32'h3F7D70A4, // 0.98 em IEEE-754
    32'hC091EB85  // -4.56 em IEEE-754
};

logic [31:0] instructions [0:23] = {
    32'bXXXXX00XXXXXXXXXX000XXXXX1000011, // FMADD.S
    32'bXXXXX00XXXXXXXXXX000XXXXX1000111, // FMSUB.S
    32'bXXXXX00XXXXXXXXXX000XXXXX1001011, // FNMSUB.S
    32'bXXXXX00XXXXXXXXXX000XXXXX1001111, // FNMADD.S
    32'b0000000XXXXXXXXXX000XXXXX1010011, // FADD.S
    32'b0000100XXXXXXXXXX000XXXXX1010011, // FSUB.S
    32'b0001000XXXXXXXXXX000XXXXX1010011, // FMUL.S
    32'b0001100XXXXXXXXXX000XXXXX1010011, // FDIV.S
    32'b010110000000XXXXX000XXXXX1010011, // FSQRT.S
    32'b0010000XXXXXXXXXX000XXXXX1010011, // FSGNJ.S
    32'b0010000XXXXXXXXXX001XXXXX1010011, // FSGNJN.S
    32'b0010000XXXXXXXXXX010XXXXX1010011, // FSGNJX.S
    32'b0010100XXXXXXXXXX000XXXXX1010011, // FMIN.S
    32'b0010100XXXXXXXXXX001XXXXX1010011, // FMAX.S
    32'b110000000000XXXXX000XXXXX1010011, // FCVT.W.S
    32'b110000000001XXXXX000XXXXX1010011, // FCVT.WU.S
    32'b111000000000XXXXX000XXXXX1010011, // FMV.X.W
    32'b101000000000XXXXX010XXXXX1010011, // FEQ.S
    32'b101000000000XXXXX001XXXXX1010011, // FLT.S
    32'b101000000000XXXXX000XXXXX1010011, // FLE.S
    32'b111000000000XXXXX001XXXXX1010011, // FCLASS.S
    32'b110100000000XXXXX000XXXXX1010011, // FCVT.S.W
    32'b110100000001XXXXX000XXXXX1010011, // FCVT.S.WU
    32'b111100000000XXXXX000XXXXX1010011  // FMV.W.X
};


initial begin

    apu_operands_i[0] = num_a[0];
    apu_operands_i[1] = num_b[0];
    apu_operands_i[2] = num_c[0];

    rst_ni = 0;
    #10;
    rst_ni = 1;
    
    apu_req_i = 0;
    inst = '0;
    
    @(negedge clk_i);

    for(int i = 0; i<24; i++) begin

        drive_instr(instructions[i]);
        
    end

    #10;
    $finish;

end

task drive_instr(logic [31:0] instr);
    @(negedge clk_i);

    inst = instr;
    apu_req_i = 1;
    
    wait(apu_gnt_o);

    @(negedge clk_i);
    apu_req_i = 0;
    
    wait(apu_rvalid_o);

    $display("%t Instr: %b", $time, inst);
    $display("%t result is 0x%h", $time, apu_rdata_o);
    res_fp = logic_to_real(apu_rdata_o);
    $display("%t result is %f", $time, res_fp);
    $display("------------------------------------------------------------------------");
    
    @(negedge clk_i);
endtask

// Function to convert 32-bit logic to real
function real logic_to_real(input logic [31:0] bits);
    int sign, exponent, mantissa;
    real result;
    
    // Extract sign, exponent, and mantissa
    sign = bits[31];
    exponent = bits[30:23] - 127;  // Exponent bias for single-precision is 127
    mantissa = {1'b1, bits[22:0]}; // Add implicit leading 1
    
    // $display("sign %0b exponent %d mantissa %h", sign, exponent, mantissa);
    
    // Calculate the floating point value
    result = mantissa * 2.0 ** (exponent - 23);
    if (sign) result = -result;
    return result;
endfunction

endmodule