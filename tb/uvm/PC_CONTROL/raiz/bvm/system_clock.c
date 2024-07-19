//----------------------------------------------------------------------
//  Copyright (c) 2017 by UFCG
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//----------------------------------------------------------------------

// Author: Elmar Melcher, UFCG
// Date:   22-Jun-2017

// This function is used by bvm_cover class to check
// coveragge at regular intervals during simulation
#include <time.h>

#ifndef SYSTEM_CLOCK_UNITS_PER_SECOND
// by default the value returned by system_clock increases once per second
#define SYSTEM_CLOCK_UNITS_PER_SECOND 1
#endif

int system_clock() {
   return (int)(clock()/(CLOCKS_PER_SEC/SYSTEM_CLOCK_UNITS_PER_SECOND));
}

