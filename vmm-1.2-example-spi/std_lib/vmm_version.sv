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


//
// Protect against multiple inclusion of this file
//
`ifndef VMM_VERSION__SV
`define VMM_VERSION__SV


`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

// /////////////////////////////////////////////
// Class: vmm_version
// Base class for defining VMM Stdlib versions 
class vmm_version;
   extern function int major();
   extern function int minor();
   extern function int patch();
   extern function string vendor();

   extern function void   display(string prefix = "");
   extern function string psdisplay(string prefix = "");
   extern function void   cfdisplay(string prefix = "");
endclass: vmm_version

// //////////////////////////////////////////// 
// Function: major 
// 
// Returns the major version number of the implemented VMM Standard Library. Should always
// return 1. 
// 
function int vmm_version::major();
   major = 1;
endfunction: major

// //////////////////////////////////////////// 
// Function: minor 
// 
// Returns the minor version number of the implemented VMM Standard Library. Should always
// return 5, if the additions and updates specified in this appendix are fully implemented.
// 
// 
//|   
//|   initial begin
//|      string minor_ver;
//|      vmm_version v = new;
//|      $sformat(minor_ver,"VMM Minor Version %d", v.minor());
//|      `vmm_note(log,minor_ver);
//|   end
function int vmm_version::minor();
   minor = 13;
endfunction: minor

// //////////////////////////////////////////// 
// Function: patch 
// 
// Returns the patch number of the implemented VMM Standard Library. The returned value
// is vendor-dependent. 
// 
function int vmm_version::patch();
   patch = 0;
endfunction: patch


function string vmm_version::vendor();
   vendor = "Synopsys";
endfunction: vendor

// //////////////////////////////////////////// 
// Function: display 
// 
// Displays the version image returned by the psdisplay() method, to the standard output.
// 
// The argument prefix is used to append a string to the content displayed by this method.
// 
// 
function void vmm_version::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

// //////////////////////////////////////////// 
// Function: psdisplay 
// 
// Creates a well formatted image of the VMM Standard Library implementation version
// information. The format is: 
// prefix VMM Version major.minor.patch (vendor) 
// 
function string vmm_version::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sVMM Version %0d.%0d.%0d (%s)",
            prefix, this.major(), this.minor(), this.patch(),this.vendor());
endfunction: psdisplay


function void vmm_version::cfdisplay(string prefix = "");
   this.display(prefix);
   $write("%s\n%sMacro Definitions:",
          prefix, prefix);

   $write("\n");
   $write("%s   VMM_CHANNEL                     %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL));
`ifdef VMM_CHANNEL_BASE
   $write("%s   VMM_CHANNEL_BASE                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL_BASE));
   $write("%s   VMM_CHANNEL_NEW_CALL            %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_CONSENSUS                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS));
`ifdef VMM_CONSENSUS_BASE
   $write("%s   VMM_CONSENSUS_BASE              %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS_BASE));
   $write("%s   VMM_CONSENSUS_NEW_CALL          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_DATA                        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA));
   $write("%s   VMM_DATA_NEW_ARGS               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_ARGS));
   $write("%s   VMM_DATA_NEW_EXTERN_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_EXTERN_ARGS));
   $write("%s   VMM_DATA_NEW_CALL               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_CALL));
`ifdef VMM_DATA_BASE
   $write("%s   VMM_DATA_BASE                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE));
  // $write("%s   VMM_DATA_BASE_NEW_ARGS          %s\n",
   //       prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_ARGS));
   //$write("%s   VMM_DATA_BASE_NEW_EXTERN_ARGS   %s\n",
    //      prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_EXTERN_ARGS));
   //$write("%s   VMM_DATA_BASE_NEW_CALL          %s\n",
    //      prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_SCENARIO                        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO));
   $write("%s   VMM_SCENARIO_NEW_ARGS               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_ARGS));
   $write("%s   VMM_SCENARIO_NEW_EXTERN_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_EXTERN_ARGS));
   $write("%s   VMM_SCENARIO_NEW_CALL               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_CALL));
   $write("%s   VMM_SCENARIO_BASE                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE));
//   $write("%s   VMM_SCENARIO_BASE_NEW_ARGS          %s\n",
  //        prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_ARGS));
   $write("%s   VMM_SCENARIO_BASE_NEW_EXTERN_ARGS   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_SCENARIO_BASE_NEW_CALL          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_CALL));

   $write("\n");
   $write("%s   VMM_ENV                         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV));
   $write("%s   VMM_ENV_NEW_ARGS                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_ARGS));
   $write("%s   VMM_ENV_NEW_EXTERN_ARGS         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_EXTERN_ARGS));
   $write("%s   VMM_ENV_NEW_CALL                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_CALL));
`ifdef VMM_ENV_BASE
   $write("%s   VMM_ENV_BASE                    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE));
   $write("%s   VMM_ENV_BASE_NEW_ARGS           %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_ARGS));
   $write("%s   VMM_ENV_BASE_NEW_EXTERN_ARGS    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_ENV_BASE_NEW_CALL           %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_LOG                         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG));
`ifdef VMM_LOG_BASE
   $write("%s   VMM_LOG_BASE                    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG_BASE));
   $write("%s   VMM_LOG_NEW_CALL                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_NOTIFY                      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY));
`ifdef VMM_NOTIFY_BASE
   $write("%s   VMM_NOTIFY_BASE                 %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY_BASE));
   $write("%s   VMM_NOTIFY_NEW_CALL             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_XACTOR                      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR));
   $write("%s   VMM_XACTOR_NEW_ARGS             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_ARGS));
   $write("%s   VMM_XACTOR_NEW_EXTERN_ARGS      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_EXTERN_ARGS));
   $write("%s   VMM_XACTOR_NEW_CALL             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_CALL));
`ifdef VMM_XACTOR_BASE
   $write("%s   VMM_XACTOR_BASE                 %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE));
   $write("%s   VMM_XACTOR_BASE_NEW_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_ARGS));
   $write("%s   VMM_XACTOR_BASE_NEW_EXTERN_ARGS %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_XACTOR_BASE_NEW_CALL        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_CALL));
`endif
endfunction: cfdisplay

`endif
