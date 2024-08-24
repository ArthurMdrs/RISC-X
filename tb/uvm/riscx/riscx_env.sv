class riscx_env extends uvm_env;

    localparam int XLEN = 32;
    localparam int ALEN = 32;

    obi_cfg   instr_obi_cfg;
    obi_cntxt instr_obi_cntxt;
    obi_vif   instr_obi_vif;

    `uvm_component_utils_begin(riscx_env)
      `uvm_field_object(instr_obi_cfg  , UVM_DEFAULT)
      `uvm_field_object(instr_obi_cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    // VIPs instances - begin
    obi_agent instr_obi_agent;
    // VIPs instances - end

    uvm_objection obj;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        
        if(obi_vif_config::get(this, "", "instr_obi_vif", instr_obi_vif))
            `uvm_info("ENV", "Virtual interface for Instr OBI was successfully set!", UVM_MEDIUM)
        else
            `uvm_error("ENV", "No interface for Instr OBI was set!")
        
        uvm_config_db#(obi_vif)::set(this, "instr_obi_agent", "vif", instr_obi_vif);
        
        instr_obi_cfg   = obi_cfg  #(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cfg"  );
        instr_obi_cntxt = obi_cntxt#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_cntxt");
        
        uvm_config_db#(obi_cfg  )::set(this, "instr_obi_agent", "cfg"  , instr_obi_cfg  );
        uvm_config_db#(obi_cntxt)::set(this, "instr_obi_agent", "cntxt", instr_obi_cntxt);

        // UVCs creation - begin
        instr_obi_agent = obi_agent#(.XLEN(XLEN),.ALEN(ALEN))::type_id::create("instr_obi_agent", this);
        // UVCs creation - end

        `uvm_info("RISC-X ENV", "Build phase running", UVM_HIGH)
        uvm_config_db#(int)::set(this, "*", "recording_detail", 1);
    endfunction

endclass: riscx_env
