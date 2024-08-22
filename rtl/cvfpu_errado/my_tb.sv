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
localparam fpnew_pkg::divsqrt_unit_t DIV_SQRT_SEL = THMULTI;

// Parameters used in vectorial operations (NOT SUPPORTED)
localparam TRUE_SIMD_CLASS  = 0;
localparam ENABLE_SIMD_MASK = 0;


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
) i_fpnew_bulk (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    // Input signals
    .operands_i     (apu_operands_i),
    .rnd_mode_i     (fp_rnd_mode),
    .op_i           (fpu_op),
    .op_mod_i       (fpu_op_mod),
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
assign fpu_op = ADDS;

// Select the operation modifier
assign fpu_op_mod = 1'b0;

// Select formats
assign fpu_int_fmt = INT32; // We only have 32-bit integers
assign fpu_src_fmt = FP32;  // We only support single-precision floats
assign fpu_dst_fmt = FP32;  // We only support single-precision floats

// Select rounding mode
assign fp_rnd_mode = RNE;


//---------------------
// Simulation
//---------------------

// Generate clock
initial begin
    clk_i = 0;
    forever
        #1 clk_i = !clk_i;
end

logic [31:0] num_a[0:9] = {
    32'hC048F5C3, // -3.14 em IEEE-754
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
    32'h3F81EB85, // 1.01 em IEEE-754
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
    32'h4091EB85, // 4.56 em IEEE-754
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



//Main simulation block
initial begin 
    real res_fp;

    rst_ni = 1'b0;
    apu_req_i = 1'b0;
    @(negedge clk_i) rst_ni = 1'b1;

    for(int i = 0; i<11; i++) begin
        apu_operands_i[0] = num_a[i];
        apu_operands_i[1] = num_b[i];
        apu_operands_i[2] = num_c[i];

        apu_req_i = 1'b1;
        wait(apu_gnt_o);
        @(negedge clk_i);
        apu_req_i = 1'b0;

        wait(apu_rvalid_o);
        $display("result is 0x%h", apu_rdata_o);
        res_fp = logic_to_real(apu_rdata_o);
        $display("result is %f", res_fp);

    end

    $finish;

end

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




/*
    logic [31:0] num_a[9:0] = {
        32'h409b_d70a,
        32'h5af2_b03c,
        32'hc2e8_9a47,
        32'h7d1c_6bfe,
        32'h3e47_8a1b,
        32'hd950_47cd,
        32'hab2f_3c8e,
        32'h8f74_1b25,
        32'haa65_b12e,
        32'hfc93_06d4
    };

    logic [31:0] num_b[9:0] = {
        32'h1f4b_c78d,
        32'h82a3_d15e,
        32'h96e7_52b4,
        32'h57d4_6c8f,
        32'h3a1b_8d67,
        32'hd2c8_f3e5,
        32'hb9a1_7c4f,
        32'h48f2_b301,
        32'hac39_04d8,
        32'h6be5_921a
    };

//Main simulation block
initial begin 
    real res_fp;

    rst_ni = 1'b0;
    apu_req_i = 1'b0;
    @(negedge clk_i) rst_ni = 1'b1;

    for(int i = 0; i<11; i++) begin
        apu_operands_i[0] = num_a[i];
        apu_operands_i[1] = num_b[i];

        apu_req_i = 1'b1;
        wait(apu_gnt_o);
        @(negedge clk_i);
        apu_req_i = 1'b0;

        wait(apu_rvalid_o);
        $display("result is 0x%h", apu_rdata_o);
        res_fp = logic_to_real(apu_rdata_o);
        $display("result is %f", res_fp);

    end

    $finish;

end
*/


//Codigo para visualizar os valores de num_a, num_b e num_c em float
/*
initial begin
    real res1, res2, res3;
    for(int i = 0; i<10; i++) begin
        
        res1 = logic_to_real(num_a[i]);
        res2 = logic_to_real(num_b[i]); 
        res3 = logic_to_real(num_c[i]); 
        $display("a is %f", res1);
        $display("b is %f", res2);
        $display("c is %f\n", res3);
    end
    $finish;
end
*/


//Main simulation block
/*
initial begin 

    real res_fp;

    rst         apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    endeq_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
        else begin
            $display("Fused multiply-subtract");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    end

    //-----------
    //FAZER O ADD
    //MAIS IMPORTANTE, CADÊ O ADD?
    //-----------

    if(fpu_op == ADDS) begin //ADDS 
        if(fpu_op_mod == 0) begin
            $display("Addition");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
        else begin
            $display("Subtraction");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    end

    if(fpu_op == MUL) begin //MUL
        $display("Multiplication");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end

    if(fpu_op == DIV) begin //DIV
        $display("Division");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end

    if(fpu_op == SQRT) begin //SQRT
        $display("Square root");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];
            apu_operands_i[2] = num_c[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end
    //-----------
    //FAZER O SGNJ
    //FAZER O MINMAX
    //FAZER O CMP
    //-----------

    //---------
    //EXEMPLO
    //---------
    for(int i = 0; i<11; i++) begin
        @(negedge clk_i);
        apu_operands_i[1] = num_a[i];
        apu_operands_i[2] = num_b[i];

        apu_req_i = 1'b1;
        wait(apu_gnt_o);
        @(negedge clk_i);
        apu_req_i = 1'b0;

        wait(apu_rvalid_o);
        $display("result in hex is 0x%h", apu_rdata_o);
        res_fp = logic_to_real(apu_rdata_o);
        $display("result in float is %f\n", res_fp);

    end

    $finish;

end
ni = 1'b0;
    apu_req_i = 1'b0;
    @(negedge clk_i) rst_ni = 1'b1;
    if(fpu_op == FMADD) begin //FMADD
        if(fpu_op_mod == 0) begin
            $display("Fused multiply-add");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
        else begin
            $display("Fused multiply-sub");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    end

    if(fpu_op == FNMSUB) begin //FNMSUB
        if(fpu_op_mod == 0) begin
            $display("Fused multiply-subtract");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    endeq_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
        else begin
            $display("Fused multiply-subtract");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[0] = num_a[i];
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    end

    //-----------
    //FAZER O ADD
    //MAIS IMPORTANTE, CADÊ O ADD?
    //-----------

    if(fpu_op == ADDS) begin //ADDS 
        if(fpu_op_mod == 0) begin
            $display("Addition");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
        else begin
            $display("Subtraction");
            for(int i = 0; i<11; i++) begin
                @(negedge clk_i);
                apu_operands_i[1] = num_b[i];
                apu_operands_i[2] = num_c[i];

                apu_req_i = 1'b1;
                wait(apu_gnt_o);
                @(negedge clk_i);
                apu_req_i = 1'b0;

                wait(apu_rvalid_o);
                $display("result in hex is 0x%h", apu_rdata_o);
                res_fp = logic_to_real(apu_rdata_o);
                $display("result in float is %f\n", res_fp);
            end
        end
    end

    if(fpu_op == MUL) begin //MUL
        $display("Multiplication");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end

    if(fpu_op == DIV) begin //DIV
        $display("Division");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end

    if(fpu_op == SQRT) begin //SQRT
        $display("Square root");
        for(int i = 0; i<11; i++) begin
            @(negedge clk_i);
            apu_operands_i[0] = num_a[i];
            apu_operands_i[1] = num_b[i];
            apu_operands_i[2] = num_c[i];

            apu_req_i = 1'b1;
            wait(apu_gnt_o);
            @(negedge clk_i);
            apu_req_i = 1'b0;

            wait(apu_rvalid_o);
            $display("result in hex is 0x%h", apu_rdata_o);
            res_fp = logic_to_real(apu_rdata_o);
            $display("result in float is %f\n", res_fp);
        end
    end
    //-----------
    //FAZER O SGNJ
    //FAZER O MINMAX
    //FAZER O CMP
    //-----------

    //---------
    //EXEMPLO
    //---------
    for(int i = 0; i<11; i++) begin
        @(negedge clk_i);
        apu_operands_i[1] = num_a[i];
        apu_operands_i[2] = num_b[i];

        apu_req_i = 1'b1;
        wait(apu_gnt_o);
        @(negedge clk_i);
        apu_req_i = 1'b0;

        wait(apu_rvalid_o);
        $display("result in hex is 0x%h", apu_rdata_o);
        res_fp = logic_to_real(apu_rdata_o);
        $display("result in float is %f\n", res_fp);

    end

    $finish;

end
*/
