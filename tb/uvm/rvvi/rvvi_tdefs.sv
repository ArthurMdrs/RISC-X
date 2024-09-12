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
// Design Name:    RVVI typedefs                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVVI typedefs.                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

typedef enum bit {
    RVVI_COV_ENABLE , 
    RVVI_COV_DISABLE
} rvvi_cov_enable_enum;

typedef enum bit {
    RVVI_LOGGING_ENABLE , 
    RVVI_LOGGING_DISABLE
} rvvi_logging_enable_enum;
