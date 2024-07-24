module rvvi_tracer (
    input  logic clk_i,
    input  logic rst_n_i,
    rvviTrace rvvi
);

string trace_file;
int cycles;
int f;

wire [31:0] pc = rvvi.pc_rdata[0][0];
wire [31:0] instr = rvvi.insn[0][0];

// cycle counter
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) cycles <= '0;
    else cycles <= cycles + 32'b1;
end

initial begin
    wait(rst_n_i == 1'b1);
    trace_file = "trace_core.log";
    // $sformat(info_tag, "CORE_TRACER %2d", hart_id_i);
    // $display("[%s] Output filename is: %s", info_tag, trace_file);
    $display("%t: Output filename is: %s", $time, trace_file);
    f = $fopen(trace_file, "w");
    $fwrite(f,"        Time |       Cycle | PC       | Instr    \n");
    $fwrite(f,"--------------------------------------------\n");
end

// final begin
//     $fclose(trace_file);
// end

// always @ (rvvi.valid) begin
always @ (negedge clk_i) begin if (rvvi.valid[0][0])
    $fwrite(f,
            "%t |%12d | %h | %h\n", $time, cycles, pc, instr);
end

endmodule