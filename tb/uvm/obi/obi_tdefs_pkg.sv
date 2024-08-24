package obi_tdefs_pkg;
    
    typedef enum bit {
        COV_ENABLE , 
        COV_DISABLE
    } obi_cov_enable_enum;

    typedef enum int {
        OBI_RST_STATE_PRE_RESET ,
        OBI_RST_STATE_IN_RESET  ,
        OBI_RST_STATE_POST_RESET
    } obi_reset_state_enum;

endpackage: obi_tdefs_pkg