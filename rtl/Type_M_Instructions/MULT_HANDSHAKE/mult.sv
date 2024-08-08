///////////////////////////////////////////////////////////////////////////////////////////////////
//
//        CLASS: ls
//  DESCRIPTION: 
//         BUGS: ---
//       AUTHOR: André Medeiros, andre.escariao1@gmail.com
// ORGANIZATION: 
//      VERSION: 1.0
//      CREATED: 08/07/2024 22:00:00 PM
//     REVISION: ---
///////////////////////////////////////////////////////////////////////////////////////////////////
module mult (
    input  logic         clock,
    input  logic         nreset,
    input  logic         valid,
    input  logic [31:0]  a,
    input  logic [31:0]  b,
    output logic [31:0]  c,
    output logic         ready
);

    logic [31:0] multiplicand;
    logic [31:0] multiplier;
    logic [31:0] product;
    logic [5:0]  count;
    logic        processing;

    always_ff @(posedge clock or posedge nreset) begin
        if (nreset) begin
            product      <= 32'b0;
            multiplicand <= 32'b0;
            multiplier   <= 32'b0;
            count        <= 6'd0;
            processing   <= 1'b0;
        end else if (valid && !processing) begin
            multiplicand <= a;
            multiplier   <= b;
            product      <= 32'b0;
            count        <= 6'd0;
            processing   <= 1'b1;
        end else if (processing) begin
            if (count < 32) begin
                if (multiplier[0] == 1'b1) begin
                    product <= product + (multiplicand);
                end
                multiplicand <= multiplicand << 1; // Desloca multiplicand para esquerda
                multiplier   <= multiplier >> 1;  // Desloca multiplier para direita
                count        <= count + 1;
            end else begin
                processing <= 1'b0;
            end
        end
    end

    always_ff @(posedge clock or posedge nreset) begin
        if (nreset) begin
            c <= 32'b0;
            ready <= 1'b0;
        end else if (!processing && ready == 1'b0) begin
            c <= product; // Usa o produto truncado para 32 bits
            ready <= 1'b1;
        end else if (valid && !processing) begin
            ready <= 1'b0;
        end
    end

endmodule
