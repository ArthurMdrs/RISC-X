
typedef enum bit {
    CLKNRST_COV_ENABLE , 
    CLKNRST_COV_DISABLE
} clknrst_cov_enable_enum;
    
typedef enum bit [1:0] {
    CLKNRST_ACTION_START_CLK   ,
    CLKNRST_ACTION_STOP_CLK    ,
    CLKNRST_ACTION_ASSERT_RESET,
    CLKNRST_ACTION_RESTART_CLK
} clknrst_action_enum;
    
typedef enum bit [1:0] {
    CLKNRST_INITIAL_VALUE_0,
    CLKNRST_INITIAL_VALUE_1,
    CLKNRST_INITIAL_VALUE_X
} clknrst_init_val_enum;
