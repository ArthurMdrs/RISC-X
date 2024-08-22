module test_tb();

    logic [31:0] inst;
	//logic [2:0] fpu_op_mod_wire;
	logic [2:0] roundmode_wire;
    logic fpu_op_mod_wire;
    logic rs1_isF_wire;
    logic rs2_isF_wire;
    logic rd_isF_wire;
    logic rs3_is_used_wire;
    logic [4:0] rs3_addr_F_wire;
    logic [4:0] is_store_wire;

    decoder dec(.instr_i(inst), .is_compressed_i(0), .roundmode_e(roundmode_wire), .fpu_op_mod(fpu_op_mod_wire), .rs1_isF_o(rs1_isF_wire), .rs2_isF_o(rs2_isF_wire), .rd_isF_o(rsd_isF_wire), .rs3_is_used_o(rs3_is_used_wire), .rs3_addr_F_o(rs3_addr_F_wire), .is_store_o(is_store_wire));


endmodule