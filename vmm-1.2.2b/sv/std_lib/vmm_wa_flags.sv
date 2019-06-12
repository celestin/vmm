//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


`ifndef VMM_WA_FLAGS__SV
`define VMM_WA_FLAGS__SV

//
// Identify work-arounds
//

// Acceptable work-arounds
`define NO_FOREACH_LOOP
`define NO_ALIAS
`define NO_RANDSTATE

// Painful work-arounds
`define NO_WAIT_ON_SIZE
`define NO_RANDOMIZE_NULL
`define NO_PROGRAM_IN_MODULE
`define NO_MULTIPLE_PROGRAMS
`define NO_SIZE_RANDOMIZATION
`define NO_DIST_ON_SIZE

// Unacceptable work-arounds 
`define NO_CLASS_IN_MODULE
`define NO_FOREACH_CONSTRAINT

// No longer required
`undef NO_SIZE_IN_CONSTRAINT
`undef NO_EXTERN_CONSTRAINT
`undef NO_EXTERN_NEW
`undef NO_CLASS_IN_ROOT
`undef NO_CLASS_ENUMS
`undef NO_NONBLOCKING_SYNC_DRIVE
`undef NO_RANDOMIZE_WITH
`undef NO_LOCAL_WAIT
`undef NO_CAST
`undef NO_DEF_ARGS_ON_EXTERN_TASK
  
`ifdef NO_FOREACH_LOOP
   `define foreach(array, idx) for (int idx = 0; idx < $size(array, 1); idx++)
`else
   `define foreach(array, idx) foreach (array[idx])
`endif

`ifdef NO_RANDSTATE
   `define get_randstate "0"
   `define set_randstate(str) while (0) $write("")
`else
   `define get_randstate get_randstate()
   `define set_randstate(str) set_randstate(str)
`endif

`endif
