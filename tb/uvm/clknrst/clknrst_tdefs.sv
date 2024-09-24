// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    Clock and reset typedefs                                   //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock and reset typedefs.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


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
