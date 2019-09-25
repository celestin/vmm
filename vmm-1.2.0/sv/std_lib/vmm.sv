//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
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
// VMM 1.2 Base classes are available by default
// This implies all base classes extend vmm_object
// Use +define+NO_VMM_12 to turn this off
`ifndef NO_VMM_12
`define VMM_12_UNDERPIN_STDLIB
`endif

`ifndef VMM_DOSFILE_CHECK
`define VMM_DOSFILE_CHECK If you get a syntax error on this line, \
        the file is corrupt. Make sure you unpack the VMM distribution \
        file with gunzip then tar, not a Windows tool
`endif


//---------------------------------------------------------------------
// Enable temporary work-arounds for features not yet implemented,
// disable language features that may not be supported by other tools,
// or VCS-specific extensions
//

`ifdef VCS
//`define VCS2006_06   // Uncomment if using VCS 2006.06 (requires -SP2-9 or later)
//`define VCS2008_09   // Uncomment if using VCS 2008.09 (requires -4 or later)
//`define VCS2008_12   // Uncomment if using VCS 2008.12
`define VCS2009_06     // Uncomment if using VCS 2009.06
`endif

`define VMM_SOLVE_BEFORE_SIZE
`ifdef VCS
`ifndef VMM_SOLVE_BEFORE_OPT
   `define VMM_SOLVE_BEFORE_OPT hard
`endif
`endif


`ifdef VCS2006_06
`define NO_STATIC_METHODS
`define NO_TYPED_AA_IDX
`define NO_STRING_CAST
`endif

`ifdef VCS2008_09
`define NO_STRING_CAST
`endif

`ifdef VCS2008_12
`define NO_STRING_CAST
`endif

`ifdef VCS2009_06
`endif


//---------------------------------------------------------------------
// Functionality that must be provided through DPI/System tasks
//
`ifndef VMM_DPI_
`define VMM_DPI_

//
// $sformatf()
//
// SV-2008 feature that may not be available. $sformat() could be used but
// with lower performance as formatted strings would be always created even
// if never used.
//
// VCS provides a precursor called $psprintf()
//
`ifndef vmm_sformatf
`define vmm_sformatf $psprintf
`endif

//
// String-matching pseudo methods.
//
// Those are built-in VCS and may eventually be part of a revision of the
// SV standard. In the meantime, they can be provided by DPI functions or
// their functionality be disabled. These DPIs are provided by the file
// $VMM_HOME/sv/std_lib/vmm_str_dpi.c
//
// Currently, they are used in vmm_log for name and instance name matching
// and in the XVCs for command parsing and interpretation.
//


`ifdef VCS
`define vmm_str_match(str, regex) str.match(regex)
`define vmm_str_prematch(str)     str.prematch()
`define vmm_str_postmatch(str)    str.postmatch()
`define vmm_str_backref(str, n)   str.backref(n)

`else
`ifdef VMM_NO_STR_DPI

`define vmm_str_match(str, regex) 0
`define vmm_str_prematch(str)     `"`"
`define vmm_str_postmatch(str)    `"`"
`define vmm_str_backref(str, n)   `"`"

`else

`define vmm_str_match(str, regex) vmm_str_match(str, regex)
`define vmm_str_prematch(str)     vmm_str_prematch()
`define vmm_str_postmatch(str)    vmm_str_postmatch()
`define vmm_str_backref(str, n)   vmm_str_backref(n+1)

`endif // VMM_NO_STR_DPI
`endif // VCS
`endif // VMM_DPI_

//
// The macros must be defined in a separate guard block to enable
// separate compilation because `define symbols are compilation symbols,
// not SV symbols that end up in the VMM package
//
`ifndef VMM_MACRO_DEFINED
`define VMM_MACRO_DEFINED

`define VMM_MACRO_TO_STRING(x) `"x`"

//---------------------------------------------------------------------
// User customization macros
//
`ifdef VMM_PRE_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_PRE_INCLUDE)
`endif

`ifdef NO_VMM_12
`include "std_lib/vmm_object.svh"
`endif 

//-----------------------------------
// VMM 1.2 macros
//
`define VMM_OBJECT_BASE_NEW_ARGS		, string name="[Anonymous]"
`define VMM_OBJECT_NEW_EXTERN_ARGS
`define VMM_OBJECT_NEW_CALL

`ifdef VMM_12_UNDERPIN_STDLIB
`ifndef VMM_OV_INTEROP 
`define VMM_PARAM_CHANNEL
`endif
`define VMM_12_UNDERPIN_VMM_DATA
`define VMM_12_UNDERPIN_VMM_CHANNEL
`define VMM_12_UNDERPIN_VMM_SUBENV
`define VMM_12_UNDERPIN_VMM_XACTOR
`define VMM_12_UNDERPIN_VMM_ENV
`define VMM_OBJECT_SET_PARENT(_child,_parent) \
    _child.set_parent_object(_parent); 
`endif
`define VMM_TEST_BASE vmm_timeline
                                                              
`ifdef VMM_12_UNDERPIN_VMM_DATA
   `define VMM_DATA_BASE vmm_object
   `define VMM_NOTIFY_BASE vmm_object
   `define VMM_CONSENSUS_BASE vmm_object
   `define VMM_DATA_NEW_ARGS
   `define VMM_DATA_NEW_EXTERN_ARGS
   `define VMM_DATA_NEW_CALL
   `define VMM_DATA_BASE_NEW_ARGS		, vmm_object parent = null, string name = ""
   `define VMM_DATA_BASE_NEW_EXTERN_ARGS	, vmm_object parent = null, string name =""
   `define VMM_DATA_BASE_NEW_CALL  		parent, name
   `define VMM_DATA_KILL_OBJECT  		if (parent == null) this.kill_object();

   `define VMM_DATA_BASE_METHODS
   `define VMM_SCENARIO_BASE_NEW_ARGS        	, string name=""
   `define VMM_SCENARIO_BASE_NEW_EXTERN_ARGS 
   `define VMM_SCENARIO_BASE_NEW_CALL        	, parent, name
   `define VMM_SCENARIO_BASE_METHODS
   `define VMM_XVC_ACTION_BASE_NEW_ARGS		, vmm_object parent=null
   `define VMM_XVC_ACTION_BASE_NEW_CALL		, name, parent
`endif

`ifdef VMM_12_UNDERPIN_VMM_CHANNEL
   `define VMM_CHANNEL_BASE                    vmm_unit
   `define VMM_CHANNEL_BASE_NEW_ARGS           ,vmm_object parent =null
   `define VMM_CHANNEL_BASE_NEW_EXTERN_ARGS    ,vmm_object parent=null
   `define VMM_CHANNEL_BASE_NEW_CALL           name,inst,parent
   `define VMM_CHANNEL_BASE_METHODS      \
                `vmm_typename(`VMM_CHANNEL) 
`endif

`ifdef VMM_12_UNDERPIN_VMM_ENV
   `define VMM_ENV_BASE                       vmm_timeline
   `define VMM_ENV_BASE_NEW_CALL              this.get_typename(),name
   `define VMM_ENV_BASE_METHODS      \
                `vmm_typename(vmm_env) 
`endif

`ifdef VMM_12_UNDERPIN_VMM_SUBENV
   `define VMM_SUBENV_BASE                    vmm_unit
   `define VMM_SUBENV_BASE_NEW_ARGS           ,vmm_object parent =null
   `define VMM_SUBENV_BASE_NEW_EXTERN_ARGS    ,vmm_object parent
   `define VMM_SUBENV_BASE_NEW_CALL           name,inst,parent
   `define VMM_SUBENV_BASE_METHODS      \
                `vmm_typename(`VMM_SUBENV) \
                virtual function void configure_ph(); \
		   if(this.state != CONFIGURED) \
                      this.configured(); \
                endfunction \
                virtual task reset_ph(); \
                      this.reset(); \
                endtask \
                virtual task start_ph(); \
		   if(this.state != STARTED) \
                      this.start(); \
                endtask \
                virtual task shutdown_ph(); \
		   if(this.state != STOPPED) \
                      this.stop(); \
                endtask \
                virtual task cleanup_ph(); \
		   if(this.state != CLEANED) \
                      this.cleanup(); \
                endtask \
                virtual function void report_ph(); \
                   this.report(); \
                endfunction  
`endif
                                                              
`ifdef VMM_12_UNDERPIN_VMM_XACTOR
   `define VMM_XACTOR_BASE         		vmm_unit
   `define VMM_XACTOR_NEW_ARGS     		,vmm_object parent =null
   `define VMM_XACTOR_NEW_EXTERN_ARGS     	,vmm_object parent =null
   `define VMM_XACTOR_NEW_CALL     		, parent
`endif

`ifdef VMM_XACTOR_BASE
   `define VMM_XACTOR_BASE_NEW_ARGS           ,vmm_object parent =null
   `define VMM_XACTOR_BASE_NEW_EXTERN_ARGS    ,vmm_object parent
   `define VMM_XACTOR_BASE_NEW_CALL           name,inst,parent
   `define VMM_XACTOR_BASE_METHODS      \
                `vmm_typename(vmm_xactor) \
                virtual task reset_ph(); \
		   if(!this.reset_it) \
                      this.reset_xactor(); \
                endtask \
                virtual task start_ph(); \
		   if(!start_it) \
                      this.start_xactor(); \
                endtask 
`endif


`ifndef VMM_DATA
   `define VMM_DATA                 vmm_data
`endif
`ifndef VMM_DATA_NEW_ARGS
   `define VMM_DATA_NEW_ARGS
   `define VMM_DATA_NEW_EXTERN_ARGS
   `define VMM_DATA_NEW_CALL
`endif
`ifndef VMM_DATA_BASE_NEW_ARGS
   `define VMM_DATA_BASE_NEW_ARGS
   `define VMM_DATA_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_DATA_BASE
   `ifndef VMM_DATA_BASE_NEW_CALL
      `define VMM_DATA_BASE_NEW_CALL
   `endif
   `ifndef VMM_DATA_KILL_OBJECT
      `define VMM_DATA_KILL_OBJECT
   `endif
`endif
`ifndef VMM_DATA_BASE_METHODS
   `define VMM_DATA_BASE_METHODS
`endif

`ifndef VMM_SCENARIO
   `define VMM_SCENARIO                      vmm_scenario
`endif
`ifndef VMM_SCENARIO_NEW_ARGS
   `define VMM_SCENARIO_NEW_ARGS             `VMM_DATA_NEW_ARGS
   `define VMM_SCENARIO_NEW_EXTERN_ARGS      `VMM_DATA_NEW_EXTERN_ARGS
   `define VMM_SCENARIO_NEW_CALL             `VMM_DATA_NEW_CALL
`endif
`ifndef VMM_SCENARIO_BASE
   `define VMM_SCENARIO_BASE                 vmm_data
`endif
`ifndef VMM_SCENARIO_BASE_NEW_ARGS
   `define VMM_SCENARIO_BASE_NEW_ARGS        `VMM_DATA_NEW_ARGS
   `define VMM_SCENARIO_BASE_NEW_EXTERN_ARGS `VMM_DATA_NEW_EXTERN_ARGS
`endif
`ifndef VMM_SCENARIO_BASE_NEW_CALL
   `define VMM_SCENARIO_BASE_NEW_CALL        `VMM_DATA_NEW_CALL
`endif
`ifndef VMM_SCENARIO_BASE_METHODS
   `define VMM_SCENARIO_BASE_METHODS
`endif

`ifndef VMM_CHANNEL
   `define VMM_CHANNEL                vmm_channel
`endif
`ifndef VMM_CHANNEL_BASE_NEW_ARGS
   `define VMM_CHANNEL_BASE_NEW_ARGS
   `define VMM_CHANNEL_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_CHANNEL_BASE
   `ifndef VMM_CHANNEL_BASE_NEW_CALL
      `define VMM_CHANNEL_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_CHANNEL_BASE_METHODS
   `define VMM_CHANNEL_BASE_METHODS
`endif

`ifndef VMM_CONSENSUS
   `define VMM_CONSENSUS                vmm_consensus
`endif
`ifdef VMM_CONSENSUS_BASE
   `ifndef VMM_CONSENSUS_BASE_NEW_CALL
      `define VMM_CONSENSUS_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_CONSENSUS_BASE_METHODS
   `define VMM_CONSENSUS_BASE_METHODS
`endif

`ifndef VMM_LOG
   `define VMM_LOG                 vmm_log
`endif
`ifdef VMM_LOG_BASE
   `ifndef VMM_LOG_BASE_NEW_CALL
      `define VMM_LOG_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_LOG_BASE_METHODS
   `define VMM_LOG_BASE_METHODS
`endif

`ifndef VMM_NOTIFY
   `define VMM_NOTIFY                 vmm_notify
`endif
`ifdef VMM_NOTIFY_BASE
   `ifndef VMM_NOTIFY_BASE_NEW_CALL
      `define VMM_NOTIFY_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_NOTIFY_BASE_METHODS
   `define VMM_NOTIFY_BASE_METHODS
`endif

`ifndef VMM_XACTOR
   `define VMM_XACTOR                 vmm_xactor
`endif
`ifndef VMM_XACTOR_NEW_ARGS
   `define VMM_XACTOR_NEW_ARGS
   `define VMM_XACTOR_NEW_EXTERN_ARGS
   `define VMM_XACTOR_NEW_CALL
`endif
`ifndef VMM_XACTOR_BASE_NEW_ARGS
   `define VMM_XACTOR_BASE_NEW_ARGS
   `define VMM_XACTOR_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_XACTOR_BASE
   `ifndef VMM_XACTOR_BASE_NEW_CALL
      `define VMM_XACTOR_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_XACTOR_BASE_METHODS
   `define VMM_XACTOR_BASE_METHODS   
`endif

`ifndef VMM_SUBENV
   `define VMM_SUBENV                 vmm_subenv
`endif
`ifndef VMM_SUBENV_NEW_ARGS
   `define VMM_SUBENV_NEW_ARGS
   `define VMM_SUBENV_NEW_EXTERN_ARGS
   `define VMM_SUBENV_NEW_CALL
`endif
`ifndef VMM_SUBENV_BASE_NEW_ARGS
   `define VMM_SUBENV_BASE_NEW_ARGS
   `define VMM_SUBENV_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_SUBENV_BASE
   `ifndef VMM_SUBENV_BASE_NEW_CALL
      `define VMM_SUBENV_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_SUBENV_BASE_METHODS
   `define VMM_SUBENV_BASE_METHODS
`endif

`ifdef VMM_OVM_INTEROP
   `ifndef VMM_OVM_ENV_BASE
      `define AVT_VMM_OVM_ENV_BASE vmm_env
   `endif
   `ifndef VMM_ENV
      `define VMM_ENV avt_vmm_ovm_env
   `endif
`endif

`ifndef VMM_ENV
   `define VMM_ENV                 vmm_env
`endif
`ifndef VMM_ENV_NEW_ARGS
   `define VMM_ENV_NEW_ARGS
   `define VMM_ENV_NEW_EXTERN_ARGS
   `define VMM_ENV_NEW_CALL
`endif
`ifndef VMM_ENV_BASE_NEW_ARGS
   `define VMM_ENV_BASE_NEW_ARGS
   `define VMM_ENV_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_ENV_BASE
   `ifndef VMM_ENV_BASE_NEW_CALL
      `define VMM_ENV_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_ENV_BASE_METHODS
   `define VMM_ENV_BASE_METHODS
`endif


//---------------------------------------------------------------------
// vmm_log ease-of-use macros
//
`ifdef VMM_LOG_FORMAT_FILE_LINE
   `ifndef __FILE__
   `define __FILE__ `"`"
   `endif
   `ifndef __LINE__
   `define __LINE__ -1
   `endif
`endif

`define vmm_warning(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_error(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_fatal(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

//
// If it is necessary to compile-out debug messages to gain every
// milligram of performance, defining this macro will take them out.
//

`ifdef VMM_NULL_LOG_MACROS

`define vmm_trace(log, msg)
`define vmm_debug(log, msg)
`define vmm_verbose(log, msg)
`define vmm_note(log, msg)
`define vmm_report(log, msg)
`define vmm_command(log, msg)
`define vmm_protocol(log, msg)
`define vmm_transaction(log, msg)
`define vmm_cycle(log, msg)
`define vmm_user(n, log, msg)

`else

`define vmm_trace(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_debug(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

     
`define vmm_verbose(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV, `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_note(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::NOTE_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::NOTE_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_report(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::REPORT_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::REPORT_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_command(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::COMMAND_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::COMMAND_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_protocol(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::PROTOCOL_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::PROTOCOL_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_transaction(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::TRANSACTION_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::TRANSACTION_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_cycle(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::CYCLE_TYP, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::CYCLE_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_user(n, log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::USER_TYP_``n, , `__FILE__, `__LINE__)) begin \
`else \
      if (log.start_msg(vmm_log::USER_TYP_``n)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`endif // VMM_NULL_LOG_MACROS

//---------------------------------------------------------------------
// vmm_vpd_str ease-of-use macros
//

`ifdef VCS2009_12
  `define VMM_TBLOG
`endif

`ifdef VMM_NO_TBLOG
  `undef VMM_TBLOG
`endif

`ifdef VMM_TBLOG
   `define vmm_vpd_str_normal(str)  \
           do \
              if (vmm_debug::global_verbosity >= vmm_debug::NORMAL_SEV) begin \
                 $tblog(0, str); \
	      end \
	   while(0);
	  
   `define vmm_vpd_str_trace(str)  \
           do \
              if (vmm_debug::global_verbosity >= vmm_debug::TRACE_SEV) begin \
                 $tblog(0, str); \
	      end \
	   while(0);

   `define vmm_vpd_str_debug(str)  \
           do \
              if (vmm_debug::global_verbosity >= vmm_debug::DEBUG_SEV) begin \
                 $tblog(0, str); \
	      end \
	   while(0);

   `define vmm_vpd_str_verbose(str)  \
           do \
              if (vmm_debug::global_verbosity >= vmm_debug::VERBOSE_SEV) begin \
                 $tblog(0, str); \
	      end \
	   while(0);
`endif



//---------------------------------------------------------------------
// Transactor callback and iterator ease-of-invocation macros
//

`define vmm_callback(facade, call) \
 \
do foreach (this.callbacks[vmm_i]) begin \
   facade cb; \
   if (!$cast(cb, this.callbacks[vmm_i])) continue; \
 \
   cb.call; \
end while (0)


`define foreach_vmm_xactor(xactor, name, inst) \
   xactor xact; \
   vmm_xactor_iter xactor_iter = new(name, inst); \
   for (vmm_xactor _xact = xactor_iter.first(); \
        _xact != null; \
        _xact = xactor_iter.next()) \
     if ($cast(xact, _xact))


//---------------------------------------------------------------------
// Other macros
//

`ifndef VMM_OBJECT_SET_PARENT
   `define VMM_OBJECT_SET_PARENT(_child, _parent)
`endif

`include "std_lib/vmm_log_macros.sv"
`include "std_lib/vmm_data_macros.sv"
`include "std_lib/vmm_scenario_macros.sv"
`include "std_lib/vmm_xactor_macros.sv"
`include "std_lib/vmm_subenv_macros.sv"
`include "std_lib/vmm_env_macros.sv"


`ifdef VMM_PARAM_CHANNEL
`define vmm_channel(T) \
typedef vmm_channel_typed#(T) T``_channel;

`define vmm_channel_(T) \
vmm_channel_typed#(T)


`else
`define vmm_channel_(T) T``_channel

//`undef vmm_channel

`define vmm_channel(T) \
class `vmm_channel_(T) extends `VMM_CHANNEL; \
 \
   function new(string name, \
                string inst, \
                int    full = 1, \
                int    empty = 0, \
                bit    fill_as_bytes = 0); \
      super.new(name, inst, full, empty, fill_as_bytes); \
   endfunction: new \
 \
   function T unput(int offset = -1); \
      $cast(unput, super.unput(offset)); \
   endfunction: unput \
 \
   /* special */ \
   function T get_t(int offset = 0); \
      $cast(get_t, super.get_t(offset)); \
   endfunction: get_t \
 \
   task get(output T obj, input int offset = 0); \
      vmm_data o; \
      super.get(o, offset); \
      $cast(obj, o); \
   endtask: get \
 \
   /* special */ \
   function T peek_t(int offset = 0); \
      $cast(peek_t, super.peek_t(offset)); \
   endfunction: peek_t \
 \
   task peek(output T obj, input int offset = 0); \
      vmm_data o; \
      super.peek(o, offset); \
      $cast(obj, o); \
   endtask: peek \
 \
   /* special */ \
   function T activate_t(int offset = 0); \
      $cast(activate_t, super.activate_t(offset)); \
   endfunction: activate_t \
 \
   task activate(output T obj, input int offset = 0); \
      vmm_data o; \
      super.activate(o, offset); \
      $cast(obj, o); \
   endtask: activate \
 \
   function T active_slot(); \
      $cast(active_slot, super.active_slot()); \
   endfunction: active_slot \
 \
   function T start(); \
      $cast(start, super.start()); \
   endfunction: start \
 \
   function T complete(vmm_data status = null); \
      $cast(complete, super.complete(status)); \
   endfunction: complete \
 \
   function T remove(); \
      $cast(remove, super.remove()); \
   endfunction: remove \
 \
   /* special */ \
   function T tee_t(); \
      $cast(tee_t, super.tee_t()); \
   endfunction: tee_t \
 \
   task tee(output T obj); \
      vmm_data o; \
      super.tee(o); \
      $cast(obj, o); \
   endtask: tee \
 \
   function T for_each(bit reset = 0); \
      $cast(for_each, super.for_each(reset)); \
   endfunction: for_each \
 \
endclass

`endif  // VMM_PARAM_CHANNEL
//`endif  // VMM_OV_INTEROP

//`endif  // VCS

//-------------------------------------------------------
// vmm_test shorthand macros
//

`define vmm_test_begin(testclassname, envclassname, doc) \
  class testclassname extends vmm_test; \
    envclassname env; \
    function new(); \
      super.new(`"testclassname`", doc); \
    endfunction \
    static testclassname testclassname``_inst = new(); \
    task run(vmm_env env); \
      $cast(this.env, env); \
      begin
     
`define vmm_test_end(testclassname) \
      end \
    endtask \
  endclass: testclassname


//-------------------------------------------------------
// shorthand macros to create callback infrastructure
//

`define vmm_create_callback(class_name) \
 class_name`` callbacks[$]; \
  \
 function void prepend_callback(class_name`` cb);  \
   if (cb == null) begin  \
      `vmm_error(this.log, "Attempting to prepend a NULL callback extension");  \
      return;  \
   end  \
  \
   foreach(this.callbacks[i]) begin  \
      if (this.callbacks[i] == cb) begin  \
         `vmm_warning(this.log, "Callback has already been registered");  \
         return;  \
      end  \
   end  \
   //Prepend new callback  \
   this.callbacks.push_front(cb);  \
endfunction: prepend_callback  \
  \
 function void append_callback(class_name`` cb);  \
   if (cb == null) begin  \
      `vmm_error(this.log, "Attempting to append a NULL callback extension");  \
      return;  \
   end  \
  \
   foreach(this.callbacks[i]) begin  \
      if (this.callbacks[i] == cb) begin  \
         `vmm_warning(this.log, "Callback has already been registered");  \
         return;  \
      end  \
   end  \
   //Append new callback  \
   this.callbacks.push_back(cb);  \
endfunction: append_callback  \
  \
function void unregister_callback(class_name`` cb);  \
   foreach(this.callbacks[i]) begin  \
      if (this.callbacks[i] == cb) begin  \
         // Unregister it  \
         this.callbacks.delete(i);  \
         return;  \
      end  \
   end  \
  \
   `vmm_warning(this.log, "Callback was not registered");  \
endfunction: unregister_callback 


`define vmm_scenario_valid_(T)          T``_scenario_valid  

`ifndef VMM_OV_INTEROP
`define vmm_atomic_gen(T, text) \
   typedef vmm_atomic_gen #(T,vmm_channel_typed#(T),text) T``_atomic_gen; \
   typedef vmm_atomic_gen_callbacks #(T,vmm_channel_typed#(T),text) T``_atomic_gen_callbacks; \

`define vmm_atomic_gen_using(T, C, text) \
   typedef vmm_atomic_gen #(T,C,text) T``_atomic_gen;
    
//`define vmm_scenario_valid_(T)          T``_scenario_valid   // Tilak
`define vmm_scenario_election_valid_(T) T``_scenario_election_valid

`define vmm_scenario_gen(T,text)  \
typedef vmm_scenario_gen#(T,text) T``_scenario_gen; \
typedef vmm_ss_scenario#(T) T``_scenario; \
typedef vmm_atomic_scenario#(T) T``_atomic_scenario; \
typedef vmm_scenario_gen_callbacks#(T, text) T``_scenario_gen_callbacks; \
typedef vmm_scenario_election#(T,text) T``_scenario_election; 

`define vmm_scenario_gen_using(T, channel_name, text) \
typedef vmm_scenario_gen#(T,text) T``_scenario_gen; \
typedef vmm_ss_scenario#(T) T``_scenario; \
typedef vmm_atomic_scenario#(T) T``_atomic_scenario; \
typedef vmm_scenario_gen_callbacks#(T, text) T``_scenario_gen_callbacks; \
typedef vmm_scenario_election#(T,text) T``_scenario_election; 
`else

`define vmm_atomic_gen_(class)           class``_atomic_gen
`define vmm_atomic_gen_callbacks_(class) class``_atomic_gen_callbacks


`define vmm_atomic_gen(class_name, text) \
`vmm_atomic_gen_using(class_name, class_name``_channel, text)

`define vmm_atomic_gen_using(class_name, channel_name, text) \
 \
typedef class `vmm_atomic_gen_(class_name); \
class `vmm_atomic_gen_callbacks_(class_name) extends vmm_xactor_callbacks; \
   virtual task post_inst_gen(`vmm_atomic_gen_(class_name) gen, \
                              class_name                   obj, \
                              ref bit                      drop); \
   endtask \
endclass \
 \
 \
class `vmm_atomic_gen_(class_name) extends `VMM_XACTOR; \
 \
   int unsigned stop_after_n_insts; \
 \
   typedef enum int {GENERATED, \
                     DONE} symbols_e; \
 \
 \
   class_name randomized_obj; \
 \
   channel_name out_chan; \
 \
   local int scenario_count; \
   local int obj_count; \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      $sformat(psdisplay, "%s [stops after #insts %0d>%0d]", \
               psdisplay, this.obj_count, this.stop_after_n_insts); \
      $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]", \
               psdisplay, prefix, this.out_chan.log.get_name(), \
               this.out_chan.log.get_instance(), this.out_chan.level(), \
               this.out_chan.full_level()); \
      if (this.randomized_obj != null) begin \
         prefix = {prefix, "Factory: "}; \
         psdisplay = {psdisplay, "\n", \
                      this.randomized_obj.psdisplay(prefix)}; \
      end \
      return psdisplay; \
   endfunction: psdisplay \
 \
   function new(string       inst, \
                int          stream_id = -1, \
                channel_name out_chan  = null `VMM_XACTOR_NEW_ARGS); \
      super.new({text, " Atomic Generator"}, inst, stream_id `VMM_XACTOR_NEW_CALL); \
 \
      if (out_chan == null) begin \
         out_chan = new({text, " Atomic Generator output channel"}, \
                         inst); \
         `VMM_OBJECT_SET_PARENT(out_chan, this) \
      end \
      this.out_chan = out_chan; \
      this.out_chan.set_producer(this); \
      this.log.is_above(this.out_chan.log); \
 \
      this.scenario_count = 0; \
      this.obj_count = 0; \
      this.stop_after_n_insts = 0; \
 \
      void'(this.notify.configure(GENERATED, vmm_notify::ONE_SHOT)); \
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF)); \
 \
      this.randomized_obj = new; \
      `VMM_OBJECT_SET_PARENT(this.randomized_obj, this) \
   endfunction: new \
 \
   virtual task inject(class_name obj, \
                       ref bit    dropped); \
      dropped = 0; \
 \
      `vmm_callback(`vmm_atomic_gen_callbacks_(class_name), \
                    post_inst_gen(this, obj, dropped)); \
 \
      if (!dropped) begin \
         this.obj_count++; \
         this.notify.indicate(GENERATED, obj); \
         this.out_chan.put(obj); \
      end \
   endtask: inject \
 \
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); \
      super.reset_xactor(rst_typ); \
 \
      this.out_chan.flush(); \
      this.scenario_count = 0; \
      this.obj_count = 0; \
 \
      if (rst_typ >= FIRM_RST) begin \
         this.notify.reset( , vmm_notify::HARD); \
      end \
 \
      if (rst_typ >= HARD_RST) begin \
         this.stop_after_n_insts = 0; \
         this.randomized_obj     = new; \
      end \
   endfunction: reset_xactor \
 \
   virtual protected task main(); \
      bit dropped; \
 \
      fork \
         super.main(); \
      join_none \
 \
      while (this.stop_after_n_insts <= 0 || \
             this.obj_count < this.stop_after_n_insts) begin \
 \
         this.wait_if_stopped(); \
 \
         this.randomized_obj.stream_id   = this.stream_id; \
         this.randomized_obj.scenario_id = this.scenario_count; \
         this.randomized_obj.data_id     = this.obj_count; \
 \
         if (!this.randomized_obj.randomize()) begin \
            `vmm_fatal(this.log, "Cannot randomize atomic instance"); \
            continue; \
         end \
 \
         begin \
            class_name obj; \
 \
            $cast(obj, this.randomized_obj.copy()); \
            `VMM_OBJECT_SET_PARENT(obj, this) \
            this.inject(obj, dropped); \
         end \
      end \
 \
      this.notify.indicate(DONE); \
      this.notify.indicate(XACTOR_STOPPED); \
      this.notify.indicate(XACTOR_IDLE); \
      this.notify.reset(XACTOR_BUSY); \
      this.scenario_count++; \
   endtask: main \
 \
endclass


`define vmm_scenario_(class)                class``_scenario
//`define vmm_scenario_valid_(class)          class``_scenario_valid
`define vmm_inject_item_scenario_(class)    class``_inject_item_scenario
`define vmm_atomic_scenario_(class)         class``_atomic_scenario
`define vmm_scenario_election_(class)       class``_scenario_election
`define vmm_scenario_election_valid_(class) class``_scenario_election_valid
`define vmm_scenario_gen_(class)            class``_scenario_gen
`define vmm_scenario_gen_callbacks_(class)  class``_scenario_gen_callbacks

`define vmm_scenario_gen(class_name, text) \
`vmm_scenario_gen_using(class_name, class_name``_channel, text)

`define vmm_scenario_gen_using(class_name, channel_name, text) \
 \
class `vmm_scenario_(class_name) extends `VMM_SCENARIO; \
 \
   static `VMM_LOG log = new(`"class_name`", "class"); \
 \
   rand class_name items[]; \
        class_name using; \
 \
   local virtual function string this_class_name(); \
      return `"`vmm_scenario_(class_name)`"; \
   endfunction: this_class_name \
 \
   local virtual function vmm_log get_vmm_log(); \
      return this.log; \
   endfunction \
 \
   local virtual function string __default_name(); \
      return {"Undefined ", text, " Scenario"}; \
   endfunction: __default_name \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      foreach (this.items[i]) begin \
         string pfx; \
         if (this.items[i] == null) continue; \
         $sformat(pfx, "%s  Item[%0d]: ", prefix, i); \
         psdisplay = {psdisplay, "\n", this.items[i].psdisplay(pfx)}; \
      end \
      if (this.using != null) begin \
         psdisplay = {psdisplay, "\n", this.using.psdisplay({prefix, "  Using: "})}; \
      end \
      return psdisplay; \
   endfunction \
 \
   constraint `vmm_scenario_valid_(class_name) { \
      items.size() == length; \
 \
`ifdef VMM_SOLVE_BEFORE_SIZE \
      solve length before items.size `VMM_SOLVE_BEFORE_OPT; \
`endif \
   } \
 \
`ifdef VMM_NO_PARENT_ARG_IN_SS_SCENARIO \
   // For backward compatibility \
   function new(`VMM_SCENARIO_NEW_ARGS); \
      super.new(null `VMM_SCENARIO_NEW_CALL); \
      using = null; \
   endfunction: new \
`else \
   function new(`VMM_SCENARIO parent = null \
                `VMM_SCENARIO_NEW_ARGS); \
      super.new(parent `VMM_SCENARIO_NEW_CALL); \
      using = null; \
   endfunction: new \
`endif \
 \
   virtual function vmm_data copy(vmm_data to = null); \
      `vmm_scenario_(class_name) cpy; \
 \
      if (to == null) cpy = new(); \
      else if (!$cast(cpy, to)) begin \
         `vmm_fatal(this.log, {"Cannot copy to non-", `VMM_MACRO_TO_STRING(`vmm_scenario_(class_name)), " instance"}); \
         return null; \
      end \
 \
      void'(super.copy(cpy)); \
      cpy.items = new [this.items.size()]; \
      foreach (this.items[i]) begin \
         if (this.items[i] == null) cpy.items[i] = null; \
         else $cast(cpy.items[i], this.items[i].copy()); \
      end \
      if (this.using == null) cpy.using = null; \
      else $cast(cpy.using, this.using.copy()); \
 \
      return cpy; \
   endfunction: copy \
 \
   function void allocate_scenario(class_name using = null); \
      this.items = new [this.get_max_length()]; \
      foreach (this.items[i]) begin \
         if (using == null) this.items[i] = new; \
         else $cast(this.items[i], using.copy()); \
         `VMM_OBJECT_SET_PARENT(this.items[i], this) \
 \
         this.items[i].stream_id   = this.stream_id; \
         this.items[i].scenario_id = this.scenario_id; \
         this.items[i].data_id     = i; \
      end \
   endfunction: allocate_scenario \
 \
   function void fill_scenario(class_name using = null); \
      int i; \
 \
      if (this.items.size() < this.get_max_length()) begin \
         this.items = new [this.get_max_length()] (this.items); \
      end \
      foreach (this.items[i]) begin \
         if (this.items[i] != null) continue; \
 \
         if (using == null) this.items[i] = new; \
         else $cast(this.items[i], using.copy()); \
         `VMM_OBJECT_SET_PARENT(this.items[i], this) \
 \
         this.items[i].stream_id   = this.stream_id; \
         this.items[i].scenario_id = this.scenario_id; \
         this.items[i].data_id     = i; \
      end \
   endfunction: fill_scenario \
 \
   function void pre_randomize(); \
      this.fill_scenario(this.using); \
   endfunction: pre_randomize \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
      int i; \
 \
      for (i = 0; i < this.length; i++) begin \
         class_name item; \
         $cast(item, this.items[i].copy()); \
`ifndef VMM_GRAB_DISABLED \
         channel.put(item,,this); \
`else \
         channel.put(item); \
`endif \
      end \
 \
      n_insts = this.length; \
   endtask: apply \
endclass \
 \
 \
class `vmm_inject_item_scenario_(class_name) extends `vmm_scenario_(class_name); \
 \
   function new(class_name obj `VMM_DATA_NEW_ARGS); \
      super.new(`VMM_DATA_NEW_CALL); \
 \
      this.items    = new [1]; \
      this.items[0] = obj; \
      this.length   = 1; \
      this.repeated = 0; \
      void'(this.define_scenario("Directed 'inject_obj()' transaction", 1)); \
   endfunction: new \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
`ifndef VMM_GRAB_DISABLED \
      channel.put(this.items[0],,this); \
`else \
      channel.put(this.items[0]); \
`endif \
      n_insts = 1; \
   endtask: apply \
 \
endclass \
 \
 \
class `vmm_atomic_scenario_(class_name) extends `vmm_scenario_(class_name); \
 \
   int unsigned ATOMIC; \
 \
   constraint atomic_scenario { \
      if (scenario_kind == ATOMIC) { \
         length == 1; \
         repeated == 0; \
      } \
   } \
 \
   function new(`VMM_DATA_NEW_ARGS); \
      super.new(`VMM_DATA_NEW_CALL); \
 \
      this.ATOMIC = this.define_scenario("Atomic", 1); \
 \
      this.scenario_kind   = this.ATOMIC; \
      this.length = 1; \
   endfunction: new \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
   endfunction:psdisplay \
 \
   function void pre_randomize(); \
      super.pre_randomize(); \
   endfunction \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
      super.apply(channel, n_insts); \
   endtask: apply \
 \
endclass \
 \
 \
class `vmm_scenario_election_(class_name); \
   int stream_id; \
   int scenario_id; \
   int unsigned n_scenarios; \
   int unsigned last_selected[$]; \
   int unsigned next_in_set; \
 \
   `vmm_scenario_(class_name) scenario_set[$]; \
 \
   rand int select; \
 \
   constraint `vmm_scenario_election_valid_(class_name) { \
      select >= 0; \
      select < n_scenarios; \
   } \
 \
   constraint round_robin { \
      select == next_in_set; \
   } \
 \
endclass \
 \
typedef class `vmm_scenario_gen_(class_name); \
 \
class `vmm_scenario_gen_callbacks_(class_name) extends vmm_xactor_callbacks; \
   virtual task pre_scenario_randomize(`vmm_scenario_gen_(class_name) gen, \
                                       ref `vmm_scenario_(class_name) scenario); \
   endtask \
 \
   virtual task post_scenario_gen(`vmm_scenario_gen_(class_name) gen, \
                                  `vmm_scenario_(class_name)     scenario, \
                                  ref bit                        dropped); \
   endtask \
endclass \
 \
 \
class `vmm_scenario_gen_(class_name) extends `VMM_XACTOR; \
 \
   int unsigned stop_after_n_insts; \
   int unsigned stop_after_n_scenarios; \
 \
   typedef enum int {GENERATED, \
                     DONE} symbols_e; \
 \
   `vmm_scenario_election_(class_name) select_scenario; \
 \
   `vmm_scenario_(class_name) scenario_set[$]; \
   protected `vmm_scenario_(class_name) scenario_registry[string]; \
 \
   channel_name out_chan; \
 \
   protected int scenario_count; \
   protected int inst_count; \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      $sformat(psdisplay, "%s [stops after #insts %0d>%0d or #scenarios %0d>%0d]", \
               psdisplay, this.inst_count, this.stop_after_n_insts, \
               this.scenario_count, this.stop_after_n_scenarios); \
      $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]", \
               psdisplay, prefix, this.out_chan.log.get_name(), \
               this.out_chan.log.get_instance(), this.out_chan.level(), \
               this.out_chan.full_level()); \
      foreach (this.scenario_registry[name]) begin \
         psdisplay = {psdisplay, "\n", \
                      this.scenario_registry[name].psdisplay(prefix)}; \
      end \
      return psdisplay; \
   endfunction: psdisplay \
 \
   function new(string       inst, \
                int          stream_id = -1, \
                channel_name out_chan  = null \
                `VMM_XACTOR_NEW_ARGS); \
      super.new({text, " Scenario Generator"}, inst, stream_id \
                `VMM_XACTOR_NEW_CALL); \
 \
      if (out_chan == null) begin \
         out_chan = new({text, " Scenario Generator output channel"}, \
                        inst); \
         `VMM_OBJECT_SET_PARENT(out_chan, this) \
      end \
      this.out_chan = out_chan; \
      this.out_chan.set_producer(this); \
      this.log.is_above(this.out_chan.log); \
 \
      this.scenario_count = 0; \
      this.inst_count = 0; \
      this.stop_after_n_insts     = 0; \
      this.stop_after_n_scenarios = 0; \
 \
      this.select_scenario = new; \
      begin \
         `vmm_atomic_scenario_(class_name) sc = new; \
         `VMM_OBJECT_SET_PARENT(sc, this) \
         this.register_scenario("Atomic", sc); \
      end \
 \
      void'(this.notify.configure(GENERATED)); \
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF)); \
   endfunction: new \
 \
   virtual function void register_scenario(string name, \
                                           `vmm_scenario_(class_name) scenario); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return; \
      end \
\
      if(this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the scenario registry", name)); \
         return; \
      end \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); \
         return; \
      end \
\
      this.scenario_registry[name] = scenario; \
\
      foreach(this.scenario_set[i]) begin \
         if(this.scenario_set[i] == scenario) \
            return; \
      end \
      this.scenario_set.push_back(scenario); \
   endfunction: register_scenario \
\
   virtual function bit scenario_exists(string name); \
        if(name == "") begin \
            `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
            return 0; \
        end \
\
        if(this.scenario_registry.exists(name)) \
            scenario_exists = 1; \
        else \
            scenario_exists = 0; \
    endfunction: scenario_exists \
\
   virtual function void replace_scenario(string name, \
                                           `vmm_scenario_(class_name) scenario); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return; \
      end \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); \
         return; \
      end \
\
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_scenario]", name)); \
         return ; \
      end \
\
      foreach(this.scenario_set[i]) begin \
         if(this.scenario_set[i] == this.scenario_registry[name]) begin \
            this.scenario_set.delete(i); \
            break; \
         end \
      end \
      this.scenario_registry[name] = scenario; \
      foreach(this.scenario_set[i]) begin \
          if(this.scenario_set[i] == scenario) \
              return; \
      end \
      this.scenario_set.push_back(scenario); \
   endfunction: replace_scenario \
\
   virtual function void get_all_scenario_names(ref string name[$]); \
      string s; \
\
      if(this.scenario_registry.first(s)) begin \
         do begin \
            name.push_back(s); \
         end while(this.scenario_registry.next(s)); \
      end \
      if(name.size() == 0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario generator registry"); \
      end \
   endfunction: get_all_scenario_names \
\
   virtual function void get_names_by_scenario(`vmm_scenario_(class_name) scenario, \
                                               ref string name[$]); \
      string s; \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
         return; \
      end \
\
      if(this.scenario_registry.first(s)) begin \
         do begin \
            if(this.scenario_registry[s] == scenario) \
               name.push_back(s); \
         end while(this.scenario_registry.next(s)); \
      end \
      if(name.size() == 0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario registry"); \
      end \
   endfunction: get_names_by_scenario \
\
   virtual function string get_scenario_name(`vmm_scenario_(class_name) scenario); \
        string s[$]; \
\
        if(scenario == null) begin \
            `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
            return ""; \
        end \
\
        this.get_names_by_scenario(scenario, s); \
\
        if(s.size()) \
            get_scenario_name = s[0]; \
        else \
            get_scenario_name = ""; \
   endfunction: get_scenario_name \
\
   virtual function int get_scenario_index(`vmm_scenario_(class_name) scenario); \
       get_scenario_index = -1; \
       foreach(this.scenario_set[i]) begin \
          if(this.scenario_set[i] == scenario) begin \
             return (get_scenario_index = i); \
          end \
       end \
       if(get_scenario_index == -1) begin \
          `vmm_warning(this.log, `vmm_sformatf("Cannot find the index for the scenario")); \
       end \
   endfunction: get_scenario_index \
\
   virtual function bit unregister_scenario(`vmm_scenario_(class_name) scenario); \
      string s; \
      unregister_scenario=0; \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
         return 0; \
      end \
      if(this.scenario_registry.first(s)) begin \
         do begin \
            if(this.scenario_registry[s] == scenario) begin \
               this.scenario_registry.delete(s); \
               unregister_scenario=1; \
            end \
         end while(this.scenario_registry.next(s)); \
      end \
      if(unregister_scenario==0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario registry"); \
      end \
      if(unregister_scenario) begin \
         foreach(this.scenario_set[i]) begin \
            if(this.scenario_set[i] == scenario) begin \
               this.scenario_set.delete(i); \
               break; \
            end \
         end \
      end \
   endfunction: unregister_scenario \
\
   virtual function `vmm_scenario_(class_name) unregister_scenario_by_name(string name); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return null; \
      end \
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the scenario registry", name)); \
         return null; \
      end \
      else begin \
         unregister_scenario_by_name = this.scenario_registry[name]; \
         foreach(this.scenario_set[i]) begin \
            if(this.scenario_set[i] == this.scenario_registry[name]) begin \
               this.scenario_set.delete(i); \
               break; \
            end \
         end \
         this.scenario_registry.delete(name); \
      end \
   endfunction: unregister_scenario_by_name \
\
   virtual function `vmm_scenario_(class_name) get_scenario(string name); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return null; \
      end \
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the scenario registry", name)); \
         return null; \
      end \
\
      get_scenario = this.scenario_registry[name]; \
      if(get_scenario == null) \
         `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario associated with it in the scenario registry", name)); \
\
   endfunction: get_scenario \
 \
   function int unsigned get_n_insts(); \
      get_n_insts = this.inst_count; \
   endfunction: get_n_insts \
 \
   function int unsigned get_n_scenarios(); \
      get_n_scenarios = this.scenario_count; \
   endfunction: get_n_scenarios \
 \
   virtual task inject_obj(class_name obj); \
      `vmm_inject_item_scenario_(class_name) scenario = new(obj); \
      this.inject(scenario); \
   endtask: inject_obj \
 \
   virtual task inject(`vmm_scenario_(class_name) scenario); \
      bit drop = 0; \
 \
      scenario.stream_id   = this.stream_id; \
      scenario.scenario_id = this.scenario_count; \
      foreach (scenario.items[i]) begin \
         scenario.items[i].stream_id   = scenario.stream_id; \
         scenario.items[i].scenario_id = scenario.scenario_id; \
         scenario.items[i].data_id     = i; \
      end \
 \
      `vmm_callback(`vmm_scenario_gen_callbacks_(class_name), \
                    post_scenario_gen(this, scenario, drop)); \
 \
      if (!drop) begin \
         this.scenario_count++; \
         this.notify.indicate(GENERATED, scenario); \
 \
         if (scenario.repeated > scenario.repeat_thresh) begin \
            `vmm_warning(this.log, `vmm_sformatf("A scenario will be repeated %0d times...", \
                                                 scenario.repeated)); \
         end \
         repeat (scenario.repeated + 1) begin \
            int unsigned n_insts = 0; \
            scenario.apply(this.out_chan, n_insts); \
            this.inst_count += n_insts; \
         end \
      end \
   endtask: inject \
 \
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); \
      super.reset_xactor(rst_typ); \
      this.scenario_count = 0; \
      this.inst_count     = 0; \
      this.out_chan.flush(); \
      `vmm_delQ(this.select_scenario.last_selected); \
 \
      if (rst_typ >= FIRM_RST) begin \
         this.notify.reset( , vmm_notify::HARD); \
      end \
 \
      if (rst_typ >= HARD_RST) begin \
         `vmm_atomic_scenario_(class_name) sc = new; \
         `VMM_OBJECT_SET_PARENT(sc, this) \
 \
         this.stop_after_n_insts     = 0; \
         this.stop_after_n_scenarios = 0; \
         this.select_scenario = new; \
         this.scenario_set.push_back(sc); \
      end \
 \
   endfunction: reset_xactor \
 \
   virtual protected task main(); \
      `vmm_scenario_(class_name) the_scenario; \
 \
      fork \
         super.main(); \
      join_none \
 \
      if(this.scenario_set.size() == 0) \
          return; \
 \
      while ((this.stop_after_n_insts <= 0 \
              || this.inst_count < this.stop_after_n_insts) \
             && (this.stop_after_n_scenarios <= 0 \
                 || this.scenario_count < this.stop_after_n_scenarios)) begin \
 \
         this.wait_if_stopped(); \
 \
         this.select_scenario.stream_id    = this.stream_id; \
         this.select_scenario.scenario_id  = this.scenario_count; \
         this.select_scenario.n_scenarios  = this.scenario_set.size(); \
         this.select_scenario.scenario_set = this.scenario_set; \
         if (this.select_scenario.last_selected.size() == 0) \
            this.select_scenario.next_in_set = 0; \
         else \
            this.select_scenario.next_in_set = ((this.select_scenario.last_selected[$] + 1) % this.scenario_set.size()); \
 \
         if (!this.select_scenario.randomize()) begin \
            `vmm_fatal(this.log, "Cannot select scenario descriptor"); \
            continue; \
         end \
 \
         if (this.select_scenario.select < 0 || \
             this.select_scenario.select >= this.scenario_set.size()) begin \
            `vmm_fatal(this.log, `vmm_sformatf("Select scenario #%0d is not within available set (0-%0d)", \
                                               this.select_scenario.select, \
                                               this.scenario_set.size()-1)); \
            continue; \
         end \
 \
         this.select_scenario.last_selected.push_back(this.select_scenario.select); \
         while (this.select_scenario.last_selected.size() > 10) begin \
            void'(this.select_scenario.last_selected.pop_front()); \
         end \
 \
         the_scenario = this.scenario_set[this.select_scenario.select]; \
         if (the_scenario == null) begin \
            `vmm_fatal(this.log, `vmm_sformatf("Selected scenario #%0d does not exist", \
                                               this.select_scenario.select)); \
            continue; \
         end \
 \
         the_scenario.stream_id   = this.stream_id; \
         the_scenario.scenario_id = this.scenario_count; \
         foreach (the_scenario.items[i]) begin \
            if (the_scenario.items[i] == null) continue; \
 \
            the_scenario.items[i].stream_id   = the_scenario.stream_id; \
            the_scenario.items[i].scenario_id = the_scenario.scenario_id; \
            the_scenario.items[i].data_id     = i; \
         end \
 \
         `vmm_callback(`vmm_scenario_gen_callbacks_(class_name), \
                       pre_scenario_randomize(this, the_scenario)); \
         if (the_scenario == null) continue; \
 \
         if (!the_scenario.randomize()) begin \
            `vmm_fatal(this.log, $psprintf("Cannot randomize scenario descriptor #%0d", \
                                           this.select_scenario.select)); \
            continue; \
         end \
 \
         this.inject(the_scenario); \
      end \
 \
      this.notify.indicate(DONE); \
      this.notify.indicate(XACTOR_STOPPED); \
      this.notify.indicate(XACTOR_IDLE); \
      this.notify.reset(XACTOR_BUSY); \
      this.scenario_count++; \
   endtask: main \
  \
endclass
`endif //VMM_OV_INTEROP

//---------------------------------------------------------------------
// Work-arounds
//

`ifdef NO_STATIC_METHODS
   `define VMM_STATIC_M
`else
   `define VMM_STATIC_M static
`endif

`ifdef NO_TYPED_AA_IDX
   `define VMM_AA_INT *
`else
   `define VMM_AA_INT int
`endif


`endif // VMM_MACRO_DEFINED
//
// End of User customization macros
//---------------------------------------------------------------------

//---------------------------------------------------------------------
// TLM macros
//
`include "std_lib/vmm_tlm_macros.sv"


//---------------------------------------------------------------------
// RAL macros
//
`ifndef VMM_RW_ADDR_WIDTH
  `ifdef VMM_RAL_ADDR_WIDTH
    `define VMM_RW_ADDR_WIDTH `VMM_RAL_ADDR_WIDTH
  `else
    `define VMM_RW_ADDR_WIDTH 64
  `endif
`endif
`ifndef VMM_RW_DATA_WIDTH
  `ifdef VMM_RAL_DATA_WIDTH
    `define VMM_RW_DATA_WIDTH `VMM_RAL_DATA_WIDTH
  `else
    `define VMM_RW_DATA_WIDTH 64
  `endif
`endif


//---------------------------------------------------------------------
// Notify observer macros
//
`define vmm_notify_observer(classname,methodname)  \
class classname``_notify_observer #(type D = vmm_data) extends vmm_notify_callbacks;  \
   classname observer;  \
   vmm_notify_callbacks cb;  \
\
   function new(classname observer, vmm_notify ntfy, int notification_id);  \
      super.new();   \
      this.observer = observer;   \
      $cast(cb,this);  \
      ntfy.append_callback(notification_id, cb);   \
   endfunction  \
\
   function void indicated(vmm_data trans);  \
      observer.methodname(trans);  \
   endfunction  \
endclass   


//---------------------------------------------------------------------
// VMM Classes declaration
//
// Detect improper definition of VMM_SB_DS_IN_STDLIB
// and cause a syntax error that will provide a clue
// about the actual cause of the problem
//
`ifdef VMM__SV
   `ifdef VMM_SB_DS_IN_STDLIB
      `ifndef VMM_SB_DS_IN_STDLIB_OK
         USAGE ERROR ERROR__Symbol_VMM_SB_DS_IN_STDLIB_defined_after_first_parsing_of_vmm_sv__Use_plus_define_plus_VMM_SB_DS_IN_STDLIB_command_line_option
      `endif
   `endif
`else
   `ifdef VMM_SB_DS_IN_STDLIB
      `define VMM_SB_DS_IN_STDLIB_OK
   `endif
`endif

//
// Protect against multiple inclusion of this file
//
`ifndef VMM__SV
`define VMM__SV

`ifndef VCS
`ifndef VMM_NO_STR_DPI
import "DPI-C" function int vmm_str_match(input string str1, input string regex);
import "DPI-C" function string vmm_str_prematch();
import "DPI-C" function string vmm_str_postmatch();
import "DPI-C" function string vmm_str_backref(int n);
`endif
`endif

`ifdef VMM_IN_PACKAGE


`ifdef VCS
(* _vcs_vmm_pkg = 1 *)
`endif
package vmm_std_lib;
`endif



`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif

`include "std_lib/vmm_version.sv"

//---------------------------------------------------------------------
// Forward declarations
//

typedef class vmm_path_match;
typedef class vmm_opts_info;
typedef class vmm_opts_info_wrapper;
typedef class vmm_opts;
typedef class vmm_log;
typedef class vmm_data;
typedef class vmm_scenario;
typedef class vmm_channel;
typedef class vmm_xactor;
typedef class vmm_notify;
typedef class vmm_consensus;
typedef class vmm_voter;
typedef class vmm_subenv;
typedef class vmm_env;
typedef class vmm_test;
typedef class vmm_test_registry;


typedef class vmm_unit;

`define vmm_path_compiled string
`define vmm_path_regexp   string

typedef class `VMM_DATA;
`ifdef VMM_DATA_BASE
typedef class `VMM_DATA_BASE;
`endif
`ifdef VMM_CHANNEL_BASE
typedef class `VMM_CHANNEL_BASE;
`endif
`ifdef VMM_CONSENSUS_BASE
typedef class `VMM_CONSENSUS_BASE;
`endif
`ifdef VMM_LOG_BASE
typedef class `VMM_LOG_BASE;
`endif
`ifdef VMM_NOTIFY_BASE
typedef class `VMM_NOTIFY_BASE;
`endif
typedef class `VMM_XACTOR;
`ifdef VMM_XACTOR_BASE
typedef class `VMM_XACTOR_BASE;
`endif
typedef class `VMM_SUBENV;
`ifdef VMM_SUBENV_BASE
typedef class `VMM_SUBENV_BASE;
`endif
`ifndef VMM_OVM_INTEROP
   typedef class `VMM_ENV;
`endif
`ifdef VMM_ENV_BASE
typedef class `VMM_ENV_BASE;
`endif

`ifdef VMM_POST_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_POST_INCLUDE)
`endif

// vmm_object loaded up by default with VMM 1.2 (onward)
`include "std_lib/vmm_object.sv"

//---------------------------------------------------------------------
// vmm_opts
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif

class vmm_opts_info;
   typedef enum {BOOL_ARGS, STR_ARGS, INT_ARGS, RANGE_ARGS, OBJ_ARGS} arg_type_e;
   typedef enum {CMD_LINE, CMD_FILE, SV_FILE} src_type_e;
   arg_type_e      arg_type = BOOL_ARGS;

   string          opt;                 //Option name
   string          sarg;                //Option argument (if any)
   string          doc;                 //Contains help information from get_.. methods
   string          fname;               //Filename in case option is specified through a command file
   int             val;                 //Integer argument value

   bit             opt_specified;       //Indicates whether option is specified (through CmdLine, Cmdfile, set..)
   bit             arg_specified;       //Indicates whether argument is specified
   bit             pat_specified;       //Indicates whether option is hierarchical or global

   int             lineno;              //Line number of the command file if the option is speficied
   static int width = 1;
   `vmm_path_regexp regexp;
   string          hier;                //Hierarchy specified (if any) 
   vmm_object      obj;                 //Object argument (used for get_object/set_object)
   int             min;                 //Min value used in case of range
   int             max;                 //Max value used in case of range
   src_type_e      src_type = CMD_LINE; //Indicates the source commandline/command file/sv file set_..
   bit             is_expected;         //Indicates whether get_.. method is expecting this option
   string          exp_hier;            //Expected hierarcy in case of hierarchical option
   int             verbosity = 0;       //Indicates verbosity. can be 0-10

   extern function new(string opt, string sarg = "");
   extern function string help(bit [12:0] id, bit is_used=0);
   extern function string psdisplay(string prefix = "");
endclass

class vmm_opts;
   static local vmm_opts_info_wrapper opts_info[string];
   static local bit                   opts_extracted;
   static       vmm_log       log  = new("vmm_opts", "class");
 
   extern `VMM_STATIC_M function bit               get_bit(input string name,
                                                           input string doc       = "",
                                                           input int    verbosity = 0,
                                                           input string fname     = "",
                                                           input int    lineno    = 0);

   extern `VMM_STATIC_M function string         get_string(input string name,
                                                           input string dflt      = "",
                                                           input string doc       = "",
                                                           input int    verbosity = 0,
                                                           input string fname     = "",
                                                           input int    lineno    = 0);

   extern `VMM_STATIC_M function int               get_int(input string  name,
                                                           input int     dflt      = 0,
                                                           input string  doc       = "",
                                                           input int     verbosity = 0,
                                                           input string  fname     = "",
                                                           input int     lineno    = 0);

   extern `VMM_STATIC_M function void            get_range(input  string name,
                                                           output int    min,
                                                           output int    max,
                                                           input  int    dflt_min,
                                                           input  int    dflt_max,
                                                           input  string doc       = "",
                                                           input  int    verbosity = 0,
                                                           input  string fname     = "",
                                                           input  int    lineno    = 0);

   extern `VMM_STATIC_M function vmm_object        get_obj(output bit       is_set,
                                                           input string     name,
                                                           input vmm_object dflt   = null,
                                                           input string     fname  = "",
                                                           input int        lineno = 0);


   extern `VMM_STATIC_M function bit        get_object_bit(output bit        is_set,
                                                           input  vmm_object obj,
                                                           input  string     name,
                                                           input  string     doc       = "",
                                                           input  int        verbosity = 0,
                                                           input  string     fname     = "",
                                                           input  int        lineno    = 0);

   extern `VMM_STATIC_M function string  get_object_string(output bit        is_set,
                                                           input  vmm_object obj,
                                                           input  string     name,
                                                           input  string     dflt      = "",
                                                           input  string     doc       = "",
                                                           input  int        verbosity = 0,
                                                           input  string     fname     = "",
                                                           input  int        lineno    = 0);

   extern `VMM_STATIC_M function int        get_object_int(output bit        is_set,
                                                           input  vmm_object obj,
                                                           input  string     name,
                                                           input  int        dflt      = 0,
                                                           input  string     doc       = "",
                                                           input  int        verbosity = 0,
                                                           input  string     fname     = "",
                                                           input  int        lineno    = 0);

   extern `VMM_STATIC_M function void     get_object_range(output bit        is_set,
                                                           input  vmm_object obj,
                                                           input  string     name,
                                                           output int        min,
                                                           output int        max,
                                                           input  int        dflt_min,
                                                           input  int        dflt_max,
                                                           input  string     doc       = "",
                                                           input  int        verbosity = 0,
                                                           input  string     fname     = "",
                                                           input  int        lineno    = 0);

   extern `VMM_STATIC_M function vmm_object get_object_obj(output bit        is_set,
                                                           input  vmm_object obj,
                                                           input  string     name,
                                                           input  vmm_object dflt   = null,
                                                           input  string     fname  = "",
                                                           input  int        lineno = 0);


   extern `VMM_STATIC_M function void              set_bit(input  string   name,
                                                           input  bit      val,
                                                           input  vmm_unit root   = null,
                                                           input  string   fname  = "",
                                                           input  int      lineno = 0);

   extern `VMM_STATIC_M function void           set_string(input  string   name,
                                                           input  string   val,
                                                           input  vmm_unit root   = null,
                                                           input  string   fname  = "",
                                                           input  int      lineno = 0);

   extern `VMM_STATIC_M function void              set_int(input  string   name,
                                                           input  int      val,
                                                           input  vmm_unit root   = null,
                                                           input  string   fname  = "",
                                                           input  int      lineno = 0);

   extern `VMM_STATIC_M function void            set_range(input  string   name,
                                                           input  int      min,
                                                           input  int      max,
                                                           input  vmm_unit root   = null,
                                                           input  string   fname  = "",
                                                           input  int      lineno = 0);

   extern `VMM_STATIC_M function void           set_object(input  string     name,
                                                           input  vmm_object obj,
                                                           input  vmm_unit   root   = null,
                                                           input  string     fname  = "",
                                                           input  int        lineno = 0);

   extern `VMM_STATIC_M function void             get_help(vmm_object root = null, 
                                                           int verbosity = 0);

   extern `VMM_STATIC_M function void             check_options_usage(int verbosity = 0);

   extern `VMM_STATIC_M local function bit extract_opts_info();

   extern `VMM_STATIC_M local function void     add_specified_option(string frmt,
                                                                     string fname = "Command Line",
                                                                     vmm_opts_info::src_type_e src_type,
                                                                     int lineno = 0);

   extern `VMM_STATIC_M local function void           parse_opts_file(string filename,
                                                                      string prefix = "");

   extern `VMM_STATIC_M local function vmm_opts_info get_opts_by_name(string name, 
                                                                      vmm_opts_info::arg_type_e arg_type, 
                                                                      int verbosity, 
                                                                      string doc, 
                                                                      string hier = "");

   extern `VMM_STATIC_M local function bit                     split(string line,
                                                                     output string argv[$]);

   extern `VMM_STATIC_M local function void           split_hiername(string pattern,
                                                                     output string name, 
                                                                     output string hier_pat);
endclass


//---------------------------------------------------------------------
// vmm_log
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_log_format;
   extern virtual function string format_msg(string name,
                                             string inst,
                                             string msg_typ,
                                             string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                             string fname,
                                             int    line,
`endif
                                             ref string lines[$]);

   extern virtual function string continue_msg(string name,
                                               string inst,
                                               string msg_typ,
                                               string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                               string fname,
                                               int    line,
`endif
                                               ref string lines[$]);

   extern virtual function string abort_on_error(int count,
                                                 int limit);

   extern virtual function string pass_or_fail(bit    pass,
                                               string name,
                                               string inst,
                                               int    fatals,
                                               int    errors,
                                               int    warnings,
                                               int    dem_errs,
                                               int    dem_warns);
endclass: vmm_log_format


`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_callbacks;
   virtual function void pre_finish(vmm_log log,
                                    ref bit finished);
   endfunction

   virtual function void pre_abort(vmm_log log);
   endfunction

   virtual function void pre_stop(vmm_log log);
   endfunction

   virtual function void pre_debug(vmm_log log);
   endfunction
endclass: vmm_log_callbacks


typedef class vmm_log_below_iter;
typedef class vmm_log_msg;
typedef class vmm_log_modifier;
typedef class vmm_log_watchpoint;
typedef class vmm_log_catcher_descr;


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_log_catcher;
    /*local*/ bit issued = 0; //set to 1 if issue function is called
    /*local*/ bit thrown = 0 ; //set to 1 if throw function is called

    virtual function  void caught(vmm_log_msg msg);
        this.throw(msg);
    endfunction
    extern virtual protected function void throw(vmm_log_msg msg);
    extern virtual protected function void issue(vmm_log_msg msg);

endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_log
`ifdef VMM_LOG_BASE
   extends `VMM_LOG_BASE
`endif
;

   //
   // Symbolic constants shared by different contexts
   //
   typedef enum int {DEFAULT
                     = -1
                     , UNCHANGED
                     = -2
                     } symbols_e;

   //
   // Symbolic constants for message types
   //
   typedef enum int {FAILURE_TYP     = 'h0001,
                     NOTE_TYP        = 'h0002,
                     DEBUG_TYP       = 'h0004,
                     REPORT_TYP      = 'h0008,
                     NOTIFY_TYP      = 'h0010,
                     TIMING_TYP      = 'h0020,
                     XHANDLING_TYP   = 'h0040,
                     PROTOCOL_TYP    = 'h0080,
                     TRANSACTION_TYP = 'h0100,
                     COMMAND_TYP     = 'h0200,
                     CYCLE_TYP       = 'h0400,
                     USER_TYP_0      = 'h0800,
                     USER_TYP_1      = 'h1000,
                     USER_TYP_2      = 'h2000,
                     INTERNAL_TYP    = 'h4000,
                     DEFAULT_TYP     = -1,
                     ALL_TYPS        = 'hFFFF
                     } types_e;

   //
   // Symbolic values for message severity
   //
   typedef enum int {FATAL_SEV   = 'h0001,
                     ERROR_SEV   = 'h0002,
                     WARNING_SEV = 'h0004,
                     NORMAL_SEV  = 'h0008,
                     TRACE_SEV   = 'h0010,
                     DEBUG_SEV   = 'h0020,
                     VERBOSE_SEV = 'h0040,
                     HIDDEN_SEV  = 'h0080,
                     IGNORE_SEV  = 'h0100,
                     DEFAULT_SEV = -1,
                     ALL_SEVS    = 'hFFFF
                     } severities_e;

   //
   // Symbolic values for simulation handling
   //
   typedef enum int {CONTINUE         = 'h0001,
                     COUNT_ERROR      = 'h0002,
                     DEBUGGER         = 'h0004,
                     DUMP_STACK       = 'h0008,
                     STOP_PROMPT      = 'h0010,
                     ABORT_SIM        = 'h0020,
                     IGNORE           = 'h0040,
                     DEFAULT_HANDLING = -1
                     } handling_e;

   //
   // Pre-defined STDOUT in case the simulator does not already define it
   //
   typedef enum int {STDOUT = 32'h8000_0001} stdout_e;

   //
   // Global control parameters
   //
   static local int    error_count = 0;     // Stop when # of errs
   static local int    error_limit = 10;    // Stop when # of errs
   static local string msg_format[$];
   static local string prefix;

   //vmm log catcher data
   static local vmm_log_catcher_descr catcher_cache[`VMM_AA_INT];
          local int catcher_ids[$];
   static local bit in_catcher = 0;

   //
   // Local control parameters
   //
   static local int dflt_lvl  = NORMAL_SEV; // Default verbosity level
   static local int force_lvl = DEFAULT_SEV; // Forced (global) verbosity level
   static local bit plus_debug;     // +vmm_log_debug was specified!

   local string  name;            // Name for this object
   local string  inst;            // Instance name for this object
   local string  orig_inst;       // Original instance name for this object

   extern function bit uses_hier_inst_name();
   extern function void use_hier_inst_name();
   extern function void use_orig_inst_name();
   local static bit     is_orig = 1;      // Which one is being used?
   local int unsigned parent_count;
   extern local function void make_hier_inst_name(string prefix = "");

   local int n_msg[`VMM_AA_INT];            // # of messages, per severities
   local int n_demoted[`VMM_AA_INT];        // # of demoted messages

   //
   // Partial message
   //
   local vmm_log_msg msg;
   local string  msg_txt[$];

   static local int    type_list[$];
   static local string type_images[`VMM_AA_INT];

   static local int    sev_list[$];
   static local string sev_images[`VMM_AA_INT];

   static local vmm_log_modifier modifier_cache[`VMM_AA_INT];
          local int modifier_ids[$];
          local int has_text_modifiers;

   static local vmm_log_watchpoint watchpoint_cache[`VMM_AA_INT];
          local int watchpoint_ids[$];

          local int enabled_typs;  // Filter if type not enableds
          local int log_lvl;       // Filter trace messages > log_lvl

   //
   // Callbacks are global to all instances
   //
   static local vmm_log_format fmt = new;
   static local int in_callbacks = 0;
   static local vmm_log_callbacks callbacks[$];

   //
   // File logging
   //
   local int fp[$];

   //
   // Iterator
   //
   local int             is_self;  // Trivial iterator?
   local bit             is_all;   // Trivial iterator?
   static local vmm_log  known[$]; // List of known logs

      /*local*/ vmm_log  below[$]; // Known logs below this one
   static local int      recurse_id = 0;
          local int      visited    = 0;

   static local string pattern[2];
   static local bit    is_pattern[2];
   static local int    known_idx = 0;
   static local int    recurse;
   static local vmm_log_below_iter recurse_stack[$];

   static vmm_opts _vmm_opts;

`ifdef VMM_LOG_BASE_METHODS
   `VMM_LOG_BASE_METHODS
`endif

   extern function new(string name,
                       string inst,
                       vmm_log under=null);


   extern virtual function void                   is_above(vmm_log log);
   extern virtual function void               is_not_above(vmm_log log);
   extern virtual function vmm_log                    copy(vmm_log to = null);

   extern virtual function void                   set_name(string name);
   extern virtual function string                 get_name();
   extern virtual function void               set_instance(string inst);
   extern virtual function string             get_instance();

   extern function void 		             reset(string name    = "/./",
                              				   string inst    = "/./",
                              			           bit    recurse = 0);
   extern function vmm_log 			  for_each();
   extern virtual function void 		      list(string name     = "/./",
                                                           string inst     = "/./",
                                                           bit    recurse  = 0);

   extern virtual function void 		   display(string prefix = "");
   extern virtual function string 		 psdisplay(string prefix = "");

   extern virtual function void 		      kill();

   //
   // Formatting
   //
   extern virtual function vmm_log_format       set_format(vmm_log_format fmt);
   extern virtual function string 	     set_typ_image(int typ, string  image);
   extern virtual function string 	     set_sev_image(int severity, 
							   string  image);

   extern /*local*/ function string 		 typ_image(int typ);
   extern /*local*/ function string 		 sev_image(int severity);
   extern /*local*/ function string 	    handling_image(int handling);
   extern local function int 		  default_handling(int severity);

   extern virtual function void 		    report(string name     = "/./",
                                		           string inst     = "/./",
                                		           bit    recurse  = 0);


   //
   // Issue messages
   //
   extern virtual function bit start_msg(int typ,
                                         int severity = DEFAULT_SEV
`ifdef VMM_LOG_FORMAT_FILE_LINE 
                                         , string fname = ""
                                         , int    line  = -1
`endif
                                         );

   extern virtual function bit text(string msg = "");
   extern virtual function void end_msg();
   extern local function void flush_msg();

   //
   // Message management
   //
   extern virtual function void  enable_types(int     typs,
                                              string  name      = "",
                                              string  inst      = "",
                                              bit     recursive = 0);
   extern virtual function void disable_types(int     typs,
                                              string  name      = "",
                                              string  inst      = "",
                                              bit     recursive = 0);
   extern virtual function int         modify(string name         = "",
                                              string inst         = "",
                                              bit    recursive    = 0,
                                              int    typ          = ALL_TYPS,
                                              int    severity     = ALL_SEVS,
                                              string text         = "",
                                              int    new_typ      = UNCHANGED,
                                              int    new_severity = UNCHANGED,
                                              int    handling     = UNCHANGED);
   extern virtual function void     unmodify(int    modification_id = -1,
                                             string name            = "",
                                             string inst            = "",
                                             bit    recursive       = 0);

   extern local function void        promote();
   extern local function void         filter();
   extern local function void         notify();

   extern virtual function void set_verbosity(int    severity,
                                             string name      = "",
                                             string inst      = "",
                                             bit    recursive = 0);
   extern function int          get_verbosity();

   //
   // File logging
   //
   extern virtual function void    log_start(int    file,
                                             string name    = "",
                                             string inst    = "",
                                             bit    recurse = 0);
   extern virtual function void     log_stop(int    file,
                                             string name    = "",
                                             string inst    = "",
                                             bit    recurse = 0);


   //
   // Manage error counts
   //
   extern virtual function void stop_after_n_errors(int n);
   extern virtual function int get_message_count(int    severity = ALL_SEVS,
                                                 string name     = "",
                                                 string inst     = "",
                                                 bit    recurse  = 0);

   //
   // Synchronize with messages
   //
   extern virtual task              wait_for_msg(string name     = "",
                                                 string inst     = "",
                                                 bit    recurse  = 0,
                                                 int    typs     = ALL_TYPS,
                                                 int    severity = ALL_SEVS,
                                                 string text     = "",
                                                 logic  issued   = 1'bx,
                                                 ref vmm_log_msg msg);

   extern virtual function int create_watchpoint(int    typs     = ALL_TYPS,
                                                 int    severity = ALL_SEVS,
                                                 string text     = "",
                                                 logic  issued   = 1'bx);
   extern virtual function void   add_watchpoint(int    watchpoint_id,
                                                 string name            = "",
                                                 string inst            = "",
                                                 bit    recurse         = 0);
   extern virtual function void remove_watchpoint(int    watchpoint_id = -1,
                                                  string name          = "",
                                                  string inst          = "",
                                                  bit    recurse       = 0);
   extern virtual task        wait_for_watchpoint(int    watchpoint_id,
                                                  ref    vmm_log_msg msg);
   extern local function void       process_catch(vmm_log_msg msg);
   extern function int                      catch(vmm_log_catcher catcher,
			                          string name = "",
			                          string inst = "",
			                          bit    recurse = 0,
			                          int    typs = ALL_TYPS,
			                          int    severity = ALL_SEVS,
			                          string text = "");
   extern function bit                    uncatch(int catcher_id);
   extern function void               uncatch_all();

   //
   // Callback Management
   //
   extern virtual function void    prepend_callback(vmm_log_callbacks cb);
   extern virtual function void     append_callback(vmm_log_callbacks cb);
   extern virtual function void unregister_callback(vmm_log_callbacks cb);




endclass: vmm_log

//------------------------------------------------------------
// vmm_debug
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_debug;
   typedef enum int {NORMAL_SEV, TRACE_SEV, DEBUG_SEV, VERBOSE_SEV} verbosity_e;
   static verbosity_e global_verbosity;
   static vmm_debug debug = new;
     
   function new();
      bit plusarg;
      string arg;
      string verbosity;
      
      vmm_debug::global_verbosity = NORMAL_SEV;
      
      plusarg = $value$plusargs("vmm_tr_verbosity=%s", arg);
      
      if (plusarg) begin
         verbosity = arg.substr(0,1);   // Only look at the 1st 2 chars
         verbosity = verbosity.tolower();
         
         if (verbosity == "no") vmm_debug::global_verbosity = NORMAL_SEV;
         else if (verbosity == "tr") vmm_debug::global_verbosity = TRACE_SEV;
         else if (verbosity == "de") vmm_debug::global_verbosity = DEBUG_SEV;
         else if (verbosity == "ve") vmm_debug::global_verbosity = VERBOSE_SEV;
         else $write("Warning: Invalid +vmm_tr_verbosity specification: \"%s\"\n", arg);
      end
      
   endfunction
endclass

typedef class vmm_tlm_export_base;
typedef class vmm_tlm_analysis_export_base;
typedef class vmm_tlm_socket_base;

`ifdef VMM_SB_DS_IN_STDLIB
`include "sb/vmm_sb.sv"
(* _vcs_vmm_class = 1 *)
class vmm_sb_ds_registration;
   vmm_sb_ds             sb;
   bit                   is_in;
   bit                   is_out;
   vmm_sb_ds::ordering_e order;
endclass
`endif


//---------------------------------------------------------------------
// vmm_notify
//

`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_notify_callbacks;
   virtual function void indicated(vmm_data status);
   endfunction
endclass

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
virtual class vmm_notification;


   virtual task indicate(ref vmm_data status);
      $write("FATAL: An instance of vmm_notification::indicate() was not overloaded or super.indicate() was called\n");
      $finish;
   endtask

   virtual task reset();
      $write("FATAL: An instance of vmm_notification::reset() was not overloaded or super.reset() was called\n");
      $finish;
   endtask

endclass


typedef class vmm_notification_config;


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_notify
`ifdef VMM_NOTIFY_BASE
   extends `VMM_NOTIFY_BASE
`endif
;
   `VMM_LOG log;

   typedef enum int {ONE_SHOT = 2,
                     BLAST    = 3,
                     ON_OFF   = 5
                     } sync_e;

   typedef enum bit {SOFT,
                     HARD} reset_e;


   local int last_notification_id = 1000000;
   local vmm_notification_config configs[`VMM_AA_INT];

   extern function new(`VMM_LOG log);

`ifdef VMM_NOTIFY_BASE_METHODS
   `VMM_NOTIFY_BASE_METHODS
`endif

   extern virtual function void                      display(string prefix = "");
   extern virtual function string                  psdisplay(string prefix = "");

   extern virtual function vmm_notify                   copy(vmm_notify to       = null);
   extern virtual function int                     configure(int notification_id = -1,
        			                             sync_e sync         = ONE_SHOT);
   extern virtual function int                 is_configured(int notification_id);

   extern virtual function bit                         is_on(int notification_id);

   extern virtual task                              wait_for(int notification_id);
   extern virtual task                          wait_for_off(int notification_id);

   extern virtual function bit                 is_waited_for(int notification_id);
   extern virtual function void                   terminated(int notification_id);

   extern virtual function vmm_data                   status(int notification_id);
   extern virtual function time                    timestamp(int notification_id);
   extern virtual function void                     indicate(int notification_id,
	            		                             vmm_data status = null);

   extern virtual function void             set_notification(int              notification_id,
    				                             vmm_notification ntfy = null);
   extern virtual function vmm_notification get_notification(int notification_id);
   extern virtual function void                        reset(int     notification_id = -1,
                                                             reset_e rst_typ         = SOFT);

   extern function void                      append_callback(int                  notification_id,
                                                             vmm_notify_callbacks cbs);
   extern function void                  unregister_callback(int                  notification_id,
                                                             vmm_notify_callbacks cbs);


`ifdef VMM_TBLOG
   extern function void                          tblog_event(vmm_debug::verbosity_e verbosity, 
                                                             string                 event_desc, 
                                                             vmm_data               data = null);
`endif





`ifdef VMM_SB_DS_IN_STDLIB
   extern function void register_vmm_sb_ds(int                   notification_id,
                                           vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(int       notification_id,
                                             vmm_sb_ds sb);
`endif

endclass


//---------------------------------------------------------------------
// vmm_data
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_data
`ifdef VMM_DATA_BASE
   extends `VMM_DATA_BASE
`endif
;

   int stream_id;
   int scenario_id;
   int data_id;

   `VMM_NOTIFY notify;
   typedef enum int {EXECUTE = 999_999,
                     STARTED = 999_998,
                     ENDED = 999_997
                     } notifications_e;
   extern function new(`VMM_LOG log = null
                       `VMM_DATA_BASE_NEW_ARGS);

`ifdef VMM_DATA_BASE_METHODS
   `VMM_DATA_BASE_METHODS
`endif

   extern function vmm_log set_log(`VMM_LOG log);

   extern local virtual function string this_class_name();
   extern local virtual function vmm_log get_vmm_log();

   extern function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);
   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);
   extern virtual protected function void copy_data(vmm_data to);

   extern virtual function bit compare(       vmm_data to,
                                       output string   diff,
                                       input  int      kind = -1);

   extern virtual function int unsigned byte_size(int kind = -1);
   extern virtual function int unsigned max_byte_size(int kind = -1);
   extern virtual function int unsigned byte_pack(ref   logic [7:0]  bytes[],
                                                  input int unsigned offset = 0,
                                                  input int          kind   = -1);
   extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                    input int unsigned    offset = 0,
                                                    input int             len    = -1,
                                                    input int             kind   = -1);
   extern virtual function bit load(int file);
   extern virtual function void save(int file);

   //
   // Methods and members to support the short-hand macros
   //
   protected static string       __vmm_prefix;
   protected static string       __vmm_image;
   protected static vmm_data     __vmm_rhs;
   protected static int          __vmm_kind;
   protected static int          __vmm_offset;
   protected static int          __vmm_len;
   protected static bit [4095:0] __vmm_maxbits;
   protected static bit          __vmm_status;
   protected static logic  [7:0] __vmm_bytes[];
   protected static bit          __vmm_done_user;
   extern virtual protected function int unsigned __vmm_byte_size(int kind = -1);

   typedef enum {DO_PRINT   ='h001,
                 DO_COPY    ='h002,
                 DO_COMPARE ='h004,
                 DO_PACK    ='h010,
                 DO_UNPACK  ='h020,
		 DO_ALL     ='hFFF} do_what_e;

   typedef enum {DO_NOCOPY      ='h001,
                 DO_REFCOPY     ='h002,
                 DO_DEEPCOPY    ='h004,
                 HOW_TO_COPY    ='h007, // OR of all DO_*COPY
                 DO_NOCOMPARE   ='h008,
                 DO_REFCOMPARE  ='h010,
                 DO_DEEPCOMPARE ='h020,
                 HOW_TO_COMPARE ='h038, // OR of all DO_*COMPARE
                 DO_NONE        ='h009, // OR of all DO_NO*
                 DO_REF         ='h012, // OR of all DO_REF*
                 DO_DEEP        ='h024, // OR of all DO_DEEP*
                 _DO_DUMMY} do_how_e;

   function void do_all(          do_what_e   what,
                              ref logic [7:0] pack[],
                        const ref logic [7:0] unpack[]);
   endfunction

   extern virtual function string do_psdisplay(string prefix = "");

   extern virtual function bit do_is_valid(bit silent = 1,
                                           int kind   = -1);
   extern virtual function vmm_data do_allocate();
   extern virtual function vmm_data do_copy(vmm_data to = null);

   extern virtual function bit do_compare(       vmm_data to,
                                          output string   diff,
                                          input  int      kind = -1);

   extern virtual function int unsigned do_byte_size(int kind = -1);
   extern virtual function int unsigned do_max_byte_size(int kind = -1);
   extern virtual function int unsigned do_byte_pack(ref   logic [7:0]  bytes[],
                                                     input int unsigned offset = 0,
                                                     input int          kind   = -1);
   extern virtual function int unsigned do_byte_unpack(const ref logic [7:0] bytes[],
                                                       input int unsigned    offset = 0,
                                                       input int             len    = -1,
                                                       input int             kind   = -1);


`ifdef VCS
   extern function int vmt_hook(vmm_xactor xactor = null,
			        vmm_data   obj    = null);


`endif
endclass: vmm_data


//---------------------------------------------------------------------
// vmm_notify_observer
//
class vmm_notify_observer #(type T=vmm_channel, type D=vmm_data) extends vmm_notify_callbacks;
   T observer;
   vmm_notify_callbacks cb;

   function new(T observer, vmm_notify ntfy, int notification_id);
      super.new();
      this.observer = observer;
      $cast(cb,this);
      ntfy.append_callback(notification_id, cb);

   endfunction

   function void indicated(vmm_data trans);
      observer.observe(trans);
   endfunction
endclass


//---------------------------------------------------------------------
// vmm_connect
//
class vmm_connect #(type T=vmm_channel, type D=vmm_data);
   vmm_notify_observer#(T,D) observer;
   /* static */ vmm_log log = new("VMM connect", "Connect Class");

   virtual function channel(ref T upstream, downstream, input string name = "", vmm_object parent = null);
      string txt;
      if( (upstream == null) && (downstream == null))
      begin
         $sformat(txt, "vmm_connect::channel() method called on null channels.");
         `vmm_fatal(this.log, txt);
      end
      if( (upstream != null) && (downstream != null))
      begin
         upstream.connect(downstream);
         $sformat(txt, "Channel %s(%s) is connected with %s(%s)", upstream.log.get_name(), 
                                                                  upstream.log.get_instance(), 
                                                                  downstream.log.get_name(), 
                                                                  downstream.log.get_instance());
         `vmm_note(upstream.log, txt);
      end
      else if ((upstream == null)	&& (downstream != null))
      begin
         upstream = downstream;
         $sformat(txt, "Upstream channel is NULL and will be same as downstream channel %s(%s)", 
                                                                  downstream.log.get_name(), 
                                                                  downstream.log.get_instance());
         `vmm_note(downstream.log, txt);
      end
      else if ((upstream != null)	&& (downstream == null))
      begin
         downstream = upstream;
         $sformat(txt, "Downstream channel is NULL and will be same as upstream channel %s(%s)", 
                                                                  upstream.log.get_name(), 
                                                                  upstream.log.get_instance());
         `vmm_note(upstream.log, txt);
      end
   endfunction

   virtual function notify(T observer, vmm_notify ntfy, int notification_id);
	this.observer = new (observer, ntfy, notification_id);
   endfunction
endclass

//---------------------------------------------------------------------
// vmm_scenario
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scenario extends `VMM_SCENARIO_BASE;

   local int    next_scenario_kind = 0;
   local int    max_length         = 0;
   local string scenario_names[`VMM_AA_INT];
   local vmm_scenario parent;

   rand int unsigned scenario_kind;
   rand int unsigned length;
   rand int unsigned  repeated       = 0;
   static int unsigned repeat_thresh = 100;

   constraint vmm_scenario_valid {
      scenario_kind >= 0;
      scenario_kind < ((next_scenario_kind == 0) ? 1 : next_scenario_kind);

      length >= 0;
      length <= max_length;

      repeated >= 0;

      solve scenario_kind before length `VMM_SOLVE_BEFORE_OPT;
   }

   constraint repetition {
      repeated == 0;
   }

   extern function new(`VMM_SCENARIO parent = null
                       `VMM_SCENARIO_BASE_NEW_ARGS);

`ifdef VMM_SCENARIO_BASE_METHODS
   `VMM_SCENARIO_BASE_METHODS
`endif

   extern local virtual function string this_class_name();
   extern local virtual function vmm_log get_vmm_log();

   extern virtual function string psdisplay(string prefix = "");

   extern function int unsigned define_scenario(string name,
                                                int unsigned max_len = 0);
   extern function void redefine_scenario(int unsigned scenario_kind,
                                          string       name,
                                          int unsigned max_len = 0);
   extern function string scenario_name(int unsigned scenario_kind = 0);
   extern local virtual function string __default_name();

   extern protected function int unsigned get_max_length();

   extern function void set_parent_scenario(vmm_scenario parent);
   extern function vmm_scenario get_parent_scenario();

   extern virtual function vmm_data copy(vmm_data to = null);
endclass: vmm_scenario


//---------------------------------------------------------------------
// vmm_ms_scenario
//
typedef class vmm_ms_scenario_gen;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario extends `VMM_SCENARIO;
    static `VMM_LOG log = new("vmm_ms_scenario", "class");
    local vmm_ms_scenario_gen context_scenario_gen;

    extern function new(`VMM_SCENARIO parent = null
                        `VMM_SCENARIO_NEW_ARGS);
    extern local virtual function string this_class_name();
    extern local virtual function string __default_name();
    extern local virtual function vmm_log get_vmm_log();

    extern virtual task execute(ref int n);

    /*local*/ extern virtual function void Xset_context_genX(vmm_ms_scenario_gen gen);
    extern virtual function vmm_ms_scenario_gen get_context_gen();

    extern virtual function string psdisplay(string prefix);
    extern virtual function vmm_ms_scenario get_ms_scenario(string scenario,
                                                            string gen = "");
    extern virtual function vmm_channel get_channel(string name);
    extern virtual task grab_channels(ref vmm_channel channels[$]);

    extern virtual function vmm_data copy(vmm_data to = null);
endclass: vmm_ms_scenario


//---------------------------------------------------------------------
// vmm_ms_scenario_election
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_election;
    int stream_id;
    int scenario_id;
    int unsigned n_scenarios;
    int unsigned last_selected[$];
    int unsigned next_in_set;

    vmm_ms_scenario scenario_set[$];
    rand int select;

    constraint vmm_ms_scenario_election_valid {
        select >= 0;
        select < n_scenarios;
    }

    constraint round_robin {
        select == next_in_set;
    }
endclass: vmm_ms_scenario_election


//---------------------------------------------------------------------
// vmm_channel
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_channel
`ifdef VMM_CHANNEL_BASE
   extends `VMM_CHANNEL_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   // Predefined notifications
   typedef enum int unsigned {FULL          = 999_999,
                              EMPTY         = 999_998,
                              PUT           = 999_997,
                              GOT           = 999_996,
                              PEEKED        = 999_995,
                              ACTIVATED     = 999_994,
                              ACT_STARTED   = 999_993,
                              ACT_COMPLETED = 999_992,
                              ACT_REMOVED   = 999_991,
                              LOCKED        = 999_990,
                              UNLOCKED      = 999_989,
                              GRABBED       = 999_988,
                              UNGRABBED     = 999_987,
                              RECORDING     = 999_986,
                              PLAYBACK      = 999_985,
                              PLAYBACK_DONE = 999_984} notifications_e;

   // Arguments for lock methods
   typedef enum bit [1:0] {SOURCE = 2'b01,
                           SINK   = 2'b10
                           } endpoints_e;

   typedef enum int unsigned {INACTIVE  = 0,
                              PENDING   = 1,
                              STARTED   = 2,
                              COMPLETED = 3
                              } active_status_e;

   static vmm_opts       _vmm_opts  = new;
   static local bit      one_log;
   static local `VMM_LOG shared_log = null;

   local int full    = 0;
   local int empty   = 0;
   local bit is_sunk = 0;

   local vmm_data data[$];
   local vmm_data tee_data[$];
   local vmm_data active;
   local active_status_e active_status;
   local event teed;
   local vmm_channel downstream;
   local event       new_connection;
   local bit tee_on = 0;
   local bit [1:0] locks;

   local bit   full_chan;
   local event item_added;
   local event item_taken;

   local int iterator;

   local int record_fp;
   local time last_record_time;
   local bit is_put;
   local bit is_playback;
   local vmm_xactor producer;
   local vmm_xactor consumer;

   local `VMM_SCENARIO grab_owners[$];

   extern function new(string       name,
                       string       inst,
                       int unsigned full           = 1,
                       int unsigned empty          = 0,
                       bit          fill_as_bytes  = 1'b0
                       `VMM_CHANNEL_BASE_NEW_EXTERN_ARGS );

`ifdef VMM_CHANNEL_BASE_METHODS
   `VMM_CHANNEL_BASE_METHODS
`endif


   virtual task observe(vmm_object D);  // For vmm_connect and vmm_notify_observe
   endtask

   extern function void reconfigure(int   full          = -1,
                                    int   empty         = -1,
                                    logic fill_as_bytes = 1'bx);
   extern function int unsigned full_level();
   extern function int unsigned empty_level();
   extern function int unsigned level();
   extern function int unsigned size();

   extern function bit is_full();
   extern function void flush();
   extern function void sink();
   extern function void flow();
   extern function void reset();

   extern function void lock(bit [1:0] who);
   extern function void unlock(bit [1:0] who);
   extern function bit  is_locked(bit [1:0] who);

   extern task grab(`VMM_SCENARIO grabber);
   extern function void ungrab(`VMM_SCENARIO grabber);
   extern function bit is_grabbed();
   extern function bit try_grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   // Define the methods for grabbing and releasing the channel
   extern local function bit check_grab_owners(`VMM_SCENARIO grabber);
   extern local function bit check_all_grab_owners(`VMM_SCENARIO grabber);
   extern local function void reset_grabbers();
   extern function void sneak(vmm_data obj, int offset = -1, `VMM_SCENARIO grabber = null);
   extern task put(vmm_data obj, int offset = -1, `VMM_SCENARIO grabber = null);
   extern task playback(output bit      success,
                        input  string   filename,
                        input  vmm_data factory,
                        input  bit      metered = 0,
                        `VMM_SCENARIO   grabber = null);
`else
   extern function void sneak(vmm_data obj, int offset = -1);
   extern task put(vmm_data obj, int offset = -1);
   extern task playback(output bit      success,
                        input  string   filename,
                        input  vmm_data factory,
                        input  bit      metered = 0);
`endif

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern function vmm_data unput(int offset = -1);

   extern task get(output vmm_data obj,
                   input  int      offset = 0);
   extern /*local*/ function void XgetX(output vmm_data obj,
                                        input  int      offset = 0);
   extern local function void X_getX(output vmm_data obj,
                                     input  int      offset = 0);
   extern task peek(output vmm_data obj,
                    input  int      offset = 0);
   extern function vmm_data try_peek(int offset = 0);
   extern task activate(output vmm_data obj,
                        input  int      offset = 0);

   extern function vmm_data active_slot();
   extern function vmm_data start();
   extern function vmm_data complete(vmm_data status = null);
   extern function vmm_data remove();
   extern function active_status_e status();

   extern function bit tee_mode(bit is_on);
   extern task tee(output vmm_data obj);

   extern function void connect(vmm_channel downstream);
   extern function vmm_data for_each(bit reset = 0);
   extern function int unsigned for_each_offset();

   extern function bit record(string filename);

   extern local function int index(int offset, string from);

   /*local*/ extern function void Xrecord_to_fileX(bit [7:0] op_code,
                                                   int offset,
                                                   time diff_time);


   extern function void set_producer(vmm_xactor producer);
   extern function void set_consumer(vmm_xactor consumer);
   extern function vmm_xactor get_producer();
   extern function vmm_xactor get_consumer();
   extern function void kill();




`ifndef VMM_GRAB_DISABLED
   extern local task block_producer(`VMM_SCENARIO grabber);
`else
   extern local task block_producer();
`endif
   extern local task block_consumer();
   extern local function void unblock_producer();

`ifdef VMM_SB_DS_IN_STDLIB
   local     vmm_sb_ds_registration _vmm_sb_ds[$];

   extern function void register_vmm_sb_ds(vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(vmm_sb_ds sb);
`endif

`ifdef VMM_TBLOG
   extern function void tblog_trans(vmm_debug::verbosity_e verbosity, string action, vmm_data data);
`endif
endclass

//------------------------------------------------------------
// vmm_tlm
//
`include "std_lib/vmm_tlm.sv"

//---------------------------------------------------------------------
// vmm_channel_typed
//
class vmm_channel_typed #(type T = vmm_data) extends vmm_channel;

   /* local */ protected vmm_tlm_b_transport_export#(vmm_channel_typed#(T),T, vmm_tlm) b_export;
   /* local */ protected vmm_tlm_nb_transport_export#(vmm_channel_typed#(T),T, vmm_tlm) nb_export;
   /* local */ protected vmm_tlm_nb_transport_fw_export#(vmm_channel_typed#(T),T, vmm_tlm) nb_fw_export;

   /* local */ protected vmm_tlm_b_transport_port#(vmm_channel_typed#(T),T, vmm_tlm) b_port;
   /* local */ protected vmm_tlm_nb_transport_port#(vmm_channel_typed#(T),T, vmm_tlm) nb_port;
   /* local */ protected vmm_tlm_nb_transport_fw_port#(vmm_channel_typed#(T),T, vmm_tlm) nb_fw_port;

   /* local */ protected vmm_tlm_analysis_port#(vmm_channel_typed#(T),T) put_ap; 
   /* local */ protected vmm_tlm_analysis_export#(vmm_channel_typed#(T),T) get_ap; 

   /* local */ T nb_pending_data[$];
   /* local */ event bi_fw_event;
   /* local */ vmm_tlm m_ph[$];
   /* local */ int is_bound;
   /* local */ int is_export;
   local vmm_data _temp;


   function new(string name,
                string inst,
                int    full = 1,
                int    empty = 0,
                bit    fill_as_bytes = 0);
      super.new(name, inst, full, empty, fill_as_bytes);
      is_bound = 0;
      is_export = 0;
   endfunction: new

   function int tlm_bind(vmm_tlm_base tlm_intf, vmm_tlm::intf_e intf, string fname = "", int lineno = 0);
      int _temp_check = 0;
      if(is_bound == 0) begin
         case(intf)
            vmm_tlm::TLM_BLOCKING_PORT: begin
               vmm_tlm_export_base#(T, vmm_tlm) t_b_export;
               if($cast(t_b_export, tlm_intf)) begin
                  b_port = new(this, "Blocking Port"); 
                  b_port.tlm_bind(t_b_export);
                  is_bound = 1;
                  fork
                  tlm_port_check_activate();  
                  join_none
               end
            end
            vmm_tlm::TLM_NONBLOCKING_PORT: begin
               vmm_tlm_socket_base#(T, vmm_tlm) t_nb_export;
               if($cast(t_nb_export, tlm_intf)) begin
                  nb_port = new(this, "Non-Blocking Port"); 
                  nb_port.tlm_bind(t_nb_export);
                  is_bound = 1;
                  fork
                  tlm_port_check_activate();  
                  join_none
               end
            end
            vmm_tlm::TLM_NONBLOCKING_FW_PORT: begin
               vmm_tlm_export_base#(T, vmm_tlm) t_nb_fw_export;
               if($cast(t_nb_fw_export, tlm_intf)) begin
                  nb_fw_port = new(this, "Non-Blocking FW Port"); 
                  nb_fw_port.tlm_bind(t_nb_fw_export);
                  is_bound = 1;
                  fork
                  tlm_port_check_activate();  
                  join_none
               end
            end
            vmm_tlm::TLM_BLOCKING_EXPORT: begin
               vmm_tlm_port_base#(T, vmm_tlm) t_b_port;
               if($cast(t_b_port, tlm_intf)) begin
                  b_export = new(this, "Blocking Export",100000); 
                  b_export.tlm_bind(t_b_port);
                  is_bound = 1;
                  is_export = 1;
               end
            end
            vmm_tlm::TLM_NONBLOCKING_EXPORT: begin
               vmm_tlm_socket_base#(T, vmm_tlm) t_nb_port;
               if($cast(t_nb_port, tlm_intf)) begin
                  nb_export = new(this, "Non-Blocking Export",100000); 
                  nb_export.tlm_bind(t_nb_port);
                  is_bound = 1;
                  fork
                  call_bw_for_bi_export(); 
                  join_none
               end
            end
            vmm_tlm::TLM_NONBLOCKING_FW_EXPORT: begin
               vmm_tlm_port_base#(T, vmm_tlm) t_nb_fw_port;
               if($cast(t_nb_fw_port, tlm_intf)) begin
                  nb_fw_export = new(this, "Non-Blocking FW Export",100000); 
                  nb_fw_export.tlm_bind(t_nb_fw_port);
                  is_bound = 1;
                  is_export = 2;
               end
            end
            vmm_tlm::TLM_ANALYSIS_PORT: begin
               vmm_tlm_analysis_export_base#(T) t_get_ap;
               if($cast(t_get_ap, tlm_intf)) begin
                  put_ap = new(this, "Analysis port");
                  put_ap.tlm_bind(t_get_ap);
                  is_bound = 1;
                  is_export = 3;
                  fork
                  tlm_port_check_activate();  
                  join_none
               end
            end
            vmm_tlm::TLM_ANALYSIS_EXPORT: begin
               vmm_tlm_analysis_port_base#(T) t_put_ap;
               if($cast(t_put_ap, tlm_intf)) begin
                  get_ap = new(this, "Analysis export",100000);
                  get_ap.tlm_bind(t_put_ap);
                  is_bound = 1;
                  is_export = 4;
               end
            end
	    default: begin
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Wrong type is passed as a first argument to tlm_bind method, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Wrong type is passed as a first argument to tlm_bind method");
               _temp_check = 1;
            end
         endcase
         if((!is_bound) && (!_temp_check) ) begin
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Channel interface and TLM interface dont match interfaces, in file %s line %d", fname, lineno));
               else
                  `vmm_error(log,"Channel interface and TLM interface dont match interfaces");
         end
      end
      else if(is_export == 1) begin
         if(intf == vmm_tlm::TLM_BLOCKING_EXPORT)
         begin
            vmm_tlm_port_base#(T, vmm_tlm) t_b_port;
            if($cast(t_b_port, tlm_intf))
               b_export.tlm_bind(t_b_port);
            else
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
         end
         else
         begin
         end
      end   
      else if(is_export == 2) begin
         if(intf == vmm_tlm::TLM_NONBLOCKING_FW_EXPORT)
         begin
            vmm_tlm_port_base#(T, vmm_tlm) t_nb_fw_port;
            if($cast(t_nb_fw_port, tlm_intf))
               nb_fw_export.tlm_bind(t_nb_fw_port);
            else
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
         end
      end
      else if(is_export == 3) begin
         if(intf == vmm_tlm::TLM_ANALYSIS_PORT)
         begin
            vmm_tlm_analysis_export_base#(T) t_get_ap;
            if($cast(t_get_ap, tlm_intf))
               put_ap.tlm_bind(t_get_ap);
            else
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
         end
      end   
      else if(is_export == 4) begin
         if(intf == vmm_tlm::TLM_ANALYSIS_EXPORT)
         begin
            vmm_tlm_analysis_port_base#(T) t_put_ap;
            if($cast(t_put_ap, tlm_intf))
               get_ap.tlm_bind(t_put_ap);
            else
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
         end
      end   
      else begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,$psprintf("Interface in the channel is already bound, in file %s line %d", fname, lineno));
         else
            `vmm_error(log,"Interface in the channel is already bound");
      end
   endfunction: tlm_bind
   
   task b_transport(int id = -1, T trans, vmm_tlm ph = null, int delay = -1);
      this.put(trans); 
      if(ph != null)
         ph.sync = vmm_tlm::TLM_COMPLETED;
   endtask : b_transport

   function vmm_tlm::sync_e nb_transport_fw(int id = -1, T trans, vmm_tlm ph = null, int delay = -1); 
      if(nb_export != null)
      begin
         this.sneak(trans);
         if(ph != null)
            m_ph.push_back(ph);
         nb_pending_data.push_back(trans);
         nb_transport_fw = vmm_tlm::TLM_ACCEPTED;
         ->bi_fw_event;
      end
      else if(nb_fw_export != null)
      begin
         this.sneak(trans);
         nb_transport_fw = vmm_tlm::TLM_ACCEPTED;
      end
   endfunction : nb_transport_fw  
   
   local task call_bw_for_bi_export();
   begin
      forever
      begin
         @bi_fw_event;
         fork
            begin
               T cur_data = nb_pending_data[$];
               int data_que[$], ph_que[$];
               vmm_tlm cur_ph = m_ph[$];
               vmm_tlm t_ph;
               T t_data;
			   if($cast(_temp,cur_data)) 
                  _temp.notify.wait_for(vmm_data::ENDED);
               data_que = nb_pending_data.find_first_index(t_data) with (t_data == cur_data);
               if(data_que.size() == 0 ) begin
                  `vmm_note(log,"Transaction received on backward path does not match any pending transaction sent on forward path");
               end
               else 
               begin
                  ph_que = m_ph.find_first_index(t_ph) with (t_ph == cur_ph);
                  this.nb_transport_bw(-1, cur_data, cur_ph); 
                  nb_pending_data.delete(data_que[0]);
                  if(ph_que.size() != 0)
                     m_ph.delete(ph_que[0]);
               end
            end
         join_none
      end
   end
   endtask: call_bw_for_bi_export 
   
   function vmm_tlm::sync_e nb_transport_bw(int id = -1, T trans, vmm_tlm ph = null, int delay = -1); 
      if(nb_export != null)
         nb_export.nb_transport_bw(trans, ph, delay);
      if(nb_port != null)
      begin
	     if($cast(_temp,trans))
            _temp.notify.indicate(vmm_data::ENDED);
      end
   endfunction : nb_transport_bw  


   function void write(int id = -1, T trans);
      this.sneak(trans);
   endfunction: write

   local task tlm_port_check_activate();
      T trans;
      fork
         while(1)
         begin
            activate(trans);
            tlm_port_call_method(trans);
         end
      join_none
   endtask : tlm_port_check_activate 

   local task tlm_port_call_method(T trans);
      vmm_tlm ph;
      if(b_port != null)
      begin
         b_port.b_transport(trans);
		 if($cast(_temp,trans))
            _temp.notify.indicate(vmm_data::ENDED);
         remove();
      end   
      if(nb_port != null)
      begin
         nb_port.nb_transport_fw(trans,ph);
         remove();
      end   
      if(nb_fw_port != null) 
      begin
         nb_fw_port.nb_transport_fw(trans);
		 if($cast(_temp,trans))
            _temp.notify.indicate(vmm_data::ENDED);
         remove();
      end   
      if(put_ap != null)
      begin
         put_ap.write(trans);
		 if($cast(_temp,trans))
            _temp.notify.indicate(vmm_data::ENDED);
         remove();
      end
   endtask : tlm_port_call_method 


   function T unput(int offset = -1);
      $cast(unput, super.unput(offset));
   endfunction: unput

   task get(output T obj, input int offset = 0);
      vmm_data o;
      super.get(o, offset);
      $cast(obj, o);
   endtask: get

   task peek(output T obj, input int offset = 0);
      vmm_data o;
      super.peek(o, offset);
      $cast(obj, o);
   endtask: peek

   function T try_peek(int offset = 0);
      vmm_data o;
      o = super.try_peek(offset);
      $cast(try_peek, o);
   endfunction: try_peek

   task activate(output T obj, input int offset = 0);
      vmm_data o;
      super.activate(o, offset);
      $cast(obj, o);
   endtask: activate

   function T active_slot();
      $cast(active_slot, super.active_slot());
   endfunction: active_slot

   function T start();
      $cast(start, super.start());
   endfunction: start

   function T complete(vmm_data status = null);
      $cast(complete, super.complete(status));
   endfunction: complete

   function T remove();
      $cast(remove, super.remove());
   endfunction: remove

   task tee(output T obj);
      vmm_data o;
      super.tee(o);
      $cast(obj, o);
   endtask: tee

   function T for_each(bit reset = 0);
      $cast(for_each, super.for_each(reset));
   endfunction: for_each




endclass



//---------------------------------------------------------------------
// vmm_consensus
//

typedef class vmm_voter;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_consensus
`ifdef VMM_CONSENSUS_BASE
   extends `VMM_CONSENSUS_BASE
`endif
;

   `VMM_LOG log;

   typedef enum int { NEW_VOTE = 999_999 } notifications_e;
   `VMM_NOTIFY notify;

   local int n_dissenters;
   local int n_forcing;

   local vmm_voter voters[$];

   extern function new(string        name,
                       string        inst);

`ifdef VMM_CONSENSUS_BASE_METHODS
   `VMM_CONSENSUS_BASE_METHODS
`endif

   extern function vmm_voter register_voter(string name);
   extern function void register_xactor(vmm_xactor xact);
   extern function void register_channel(vmm_channel chan);
   extern function void register_notification(vmm_notify notify,
                                              int notification);
   extern function void register_no_notification(vmm_notify notify,
                                                 int notification);
   extern function void register_consensus(vmm_consensus vote,
                                           bit force_through = 0);

   extern function void unregister_voter(vmm_voter voter);
   extern function void unregister_xactor(vmm_xactor xact);
   extern function void unregister_channel(vmm_channel chan);
   extern function void unregister_notification(vmm_notify notify,
                                                int notification);
   extern function void unregister_consensus(vmm_consensus vote);
   extern function void unregister_all();

   extern task wait_for_consensus();
   extern task wait_for_no_consensus();
   extern function bit is_reached();
   extern function bit is_forced();

   extern virtual function string psdisplay(string prefix = "");
   extern function void yeas(ref string who[],
                             ref string why[]);
   extern function void nays(ref string who[],
                             ref string why[]);
   extern function void forcing(ref string who[],
                                ref string why[]);


   event new_results;
   extern /*local*/ function void XvoteX(bit was_agree,
                                         bit agree,
                                         bit was_forced,
                                         bit forced);
                                         
`ifdef VMM_TBLOG
   extern function void tblog_result(vmm_debug::verbosity_e verbosity, string action);
`endif   
endclass: vmm_consensus

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_voter;
   local string name;
   local vmm_consensus consensus;
   local bit vote;
   local bit is_forced;
   local string why;
   local event killme;
   local vmm_xactor xactor_voter;
   local vmm_channel channel_voter;
   local vmm_notify  notify_voter;
   local int         notification;
   local vmm_consensus sub_vote;

   // Constructor is undocumented
   extern /*local*/ function new(string        name,
                                 vmm_consensus vote);

   extern function void oppose(string why = "No reason specified");
   extern function void consent(string why = "No reason specified");
   extern function void forced(string why = "No reason specified");

   // These methods are not documented either
   extern /*local*/ function string get_name();
   extern /*local*/ function bit    get_vote();
   extern /*local*/ function bit    get_forced();
   extern /*local*/ function string get_reason();
   extern /*local*/ function void xactor(vmm_xactor xact);
   extern /*local*/ function void channel(vmm_channel chan);
   extern /*local*/ function void notify(vmm_notify ntfy, int notification, bit is_on);
   extern /*local*/ function void sub_consensus(vmm_consensus vote, bit force_through);
   extern /*local*/ function void kill_voter();
   extern /*local*/ function vmm_xactor get_xactor();
   extern /*local*/ function vmm_channel get_channel();
   extern /*local*/ function vmm_notify  get_notify();
   extern /*local*/ function int         get_notification();
   extern /*local*/ function vmm_consensus get_consensus();
endclass


//---------------------------------------------------------------------
// vmm_env
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_env
`ifdef VMM_ENV_BASE
   extends `VMM_ENV_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   typedef enum int unsigned {GEN_CFG = 1,
                              BUILD,
                              RESET_DUT,
                              CFG_DUT,
                              START,
                              RESTART,
                              WAIT_FOR_END,
                              STOP,
                              CLEANUP,
                              REPORT,
                              RESTARTED} notifications_e;

   typedef enum int unsigned {HARD, SOFT, FIRM} restart_e;

   event          end_test;
   `VMM_CONSENSUS end_vote;

   protected int step;

   local bit             reset_rng_state;
   local string thread_rng_state_after_new;
   local string thread_rng_state_after_pre_test;
   local string thread_rng_state_before_start;

   local bit soft_restart;
   local bit soft_restartable;

`ifdef VMM_OVM_INTEROP
   bit disable_ovm = 0;
`endif

   static vmm_opts _vmm_opts = new;
   static local vmm_env singleton = null;

   extern function new(string name = "Verif Env"
                       `VMM_ENV_BASE_NEW_ARGS);

`ifdef VMM_ENV_BASE_METHODS
   `VMM_ENV_BASE_METHODS
`endif

   extern virtual function string psdisplay(string prefix = "");

   extern task run();

   extern virtual protected task reset_env(restart_e kind);

   extern virtual protected task power_on_reset();
   extern virtual task hw_reset();

   extern virtual task power_up();

   extern task pre_test();
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   extern virtual task start();
   extern virtual task wait_for_end();
   extern virtual task stop();
   extern virtual task cleanup();
   extern virtual task restart(bit reconfig = 0);
   extern virtual task restart_test();
   extern virtual task report();

`ifdef VMM_TBLOG
   extern function void tblog_step(vmm_debug::verbosity_e verbosity, string step_name);
`endif


   extern virtual protected function void save_rng_state();
   extern virtual protected function void restore_rng_state();

   //
   // Methods and members to support the short-hand macros
   //
   protected static string    __vmm_prefix;
   protected static string    __vmm_image;
   protected        bit       __vmm_done_user;
   protected        int       __vmm_forks;
   protected        restart_e __vmm_restart;

   typedef enum {DO_PRINT   ='h001,
                 DO_START   ='h002,
                 DO_STOP    ='h004,
                 DO_RESET   ='h008,
                 DO_VOTE    ='h010,
		 DO_ALL     ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_env::restart_e restart_kind = vmm_env::FIRM);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual task do_vote();
   extern protected virtual task do_start();
   extern protected virtual task do_stop();
   extern protected virtual task do_reset(vmm_env::restart_e kind);

endclass


//---------------------------------------------------------------------
// vmm_subenv
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_subenv
`ifdef VMM_SUBENV_BASE
   extends `VMM_SUBENV_BASE
`endif
;
   `VMM_LOG    log;

   protected `VMM_CONSENSUS end_test;

   local enum {NEWED, CONFIGURED, STARTED, STOPPED, CLEANED} state = NEWED;

   extern function new(string         name,
                       string         inst,
                       `VMM_CONSENSUS end_test
                       `VMM_SUBENV_BASE_NEW_ARGS);

`ifdef VMM_SUBENV_BASE_METHODS
   `VMM_SUBENV_BASE_METHODS
`endif

   extern virtual function string psdisplay(string prefix = "");

   extern function vmm_consensus get_consensus();

   extern protected function void configured();

   extern virtual task start();
   extern virtual task stop();
   extern virtual task reset(vmm_env::restart_e kind = vmm_env::FIRM);
   extern virtual task cleanup();
   extern virtual function void report();
   
`ifdef VMM_TBLOG
   extern function void tblog_step(vmm_debug::verbosity_e verbosity, string step_name);
`endif

   //
   // Methods and members to support the short-hand macros
   //
   protected static string             __vmm_prefix;
   protected static string             __vmm_image;
   protected        bit                __vmm_done_user;
   protected        int                __vmm_forks;
   protected        vmm_env::restart_e __vmm_restart;

   typedef enum {DO_PRINT ='h001,
                 DO_START ='h002,
                 DO_STOP  ='h004,
                 DO_RESET ='h008,
                 DO_VOTE  ='h010,
		 DO_ALL   ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_env::restart_e restart_kind = vmm_env::FIRM);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual task do_vote();
   extern protected virtual task do_start();
   extern protected virtual task do_stop();
   extern protected virtual task do_reset(vmm_env::restart_e kind);

endclass: vmm_subenv


//---------------------------------------------------------------------
// vmm_xactor
//


`ifdef VCS
(* vmm_callback_class, _vcs_vmm_class = 1 *)
`endif
virtual class vmm_xactor_callbacks;
endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_xactor
`ifdef VMM_XACTOR_BASE
   extends `VMM_XACTOR_BASE
`endif
;
   `VMM_LOG    log;
   `VMM_NOTIFY notify;

   int stream_id;

   typedef enum int {XACTOR_IDLE        = 999999,
                     XACTOR_BUSY        = 999998,
                     XACTOR_STARTED     = 999997,
                     XACTOR_STOPPED     = 999996,
                     XACTOR_RESET       = 999995,
                     XACTOR_STOPPING    = 999994,
                     XACTOR_IS_STOPPED  = 999993
                     } notifications_e;

   local bit start_it;
   local bit stop_it;
   local bit reset_it;
   local event control_event;
   local int n_threads_to_stop;
   local int n_threads_stopped;
   local bit is_stopped;
   protected int reset_pending = 0;

   local bit main_running;

   local bit save_main_rng_state;
   local bit restore_main_rng_state;
   local string main_rng_state;
  
   /*local*/ vmm_channel Xinput_chansX[$];
   /*local*/ vmm_channel Xoutput_chansX[$];   
   /*local*/ static vmm_xactor _vmm_available_xactor[$];

   /*protected*/ vmm_xactor_callbacks callbacks[$];

   extern function new(string name,
	    	       string inst,
		       int    stream_id = -1
                       `VMM_XACTOR_BASE_NEW_ARGS);

   extern virtual function void kill();

`ifdef VMM_XACTOR_BASE_METHODS
   `VMM_XACTOR_BASE_METHODS
`endif




   typedef enum int {SOFT_RST,
                     PROTOCOL_RST,
                     FIRM_RST,
                     HARD_RST} reset_e;

   extern virtual function string get_name();
   extern virtual function string get_instance();

   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

   extern virtual function void save_rng_state();
   extern virtual function void restore_rng_state();

   extern virtual function string psdisplay(string prefix = "");
   extern virtual function void xactor_status(string prefix = "");

   extern virtual protected task main();
   extern local function void check_all_threads_stopped();
   extern protected task wait_if_stopped(int unsigned n_threads = 1);
   extern protected task wait_if_stopped_or_empty(vmm_channel  chan,
                                                  int unsigned n_threads = 1);

   extern virtual function void prepend_callback(vmm_xactor_callbacks cb);
   extern virtual function void append_callback(vmm_xactor_callbacks cb);
   extern virtual function void unregister_callback(vmm_xactor_callbacks cb);

   extern function void get_input_channels(ref vmm_channel chans[$]);
   extern function void get_output_channels(ref vmm_channel chans[$]);


`ifdef VMM_TBLOG
   extern function void tblog_state(vmm_debug::verbosity_e verbosity, string state_name);
`endif





`ifdef VMM_SB_DS_IN_STDLIB
   local     vmm_sb_ds_registration _vmm_sb_ds[$];

   extern protected function void inp_vmm_sb_ds(vmm_data tr);
   extern protected function void exp_vmm_sb_ds(vmm_data tr);
   extern function void register_vmm_sb_ds(vmm_sb_ds             sb,
                                           vmm_sb_ds::kind_e     kind,
                                           vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   extern function void unregister_vmm_sb_ds(vmm_sb_ds sb);
`endif

   //
   // Methods and members to support the short-hand macros
   //
   protected static string  __vmm_prefix;
   protected static string  __vmm_image;
   protected static bit     __vmm_done_user;

   typedef enum {DO_PRINT   ='h001,
                 DO_START   ='h002,
                 DO_STOP    ='h004,
                 DO_RESET   ='h010,
                 DO_KILL    ='h020,
		 DO_ALL     ='hFFF} do_what_e;


   function void do_all(do_what_e what,
                        vmm_xactor::reset_e   rst_typ = SOFT_RST);
   endfunction

   extern protected virtual function string do_psdisplay(string prefix = "");
   extern protected virtual function void do_start_xactor();
   extern protected virtual function void do_stop_xactor();
   extern protected virtual function void do_reset_xactor(vmm_xactor::reset_e rst_typ);
   extern protected virtual function void do_kill_xactor();
endclass

`include "std_lib/vmm_atomic_gen.sv"

//---------------------------------------------------------------------
// vmm_scenario
//
class vmm_ss_scenario_base extends `VMM_SCENARIO;
   extern function new(`VMM_SCENARIO parent = null `VMM_SCENARIO_NEW_ARGS);
   extern /*local*/ virtual function void Xset_allocate_idX(vmm_data tr, int idx = -1);
endclass


class vmm_ss_scenario#(type T=vmm_data) extends vmm_ss_scenario_base;
   /* static */ `VMM_LOG log = new( $typename(T), "class");
   rand T items[]; 
   T using; 

   extern local virtual function string this_class_name();
   extern local virtual function vmm_log get_vmm_log();
   extern local virtual function string __default_name(); 
   extern virtual function string psdisplay(string prefix = "");
   extern function new(`VMM_SCENARIO_NEW_ARGS); 
   extern virtual function vmm_data copy(vmm_data to = null); 
   extern /*local*/ virtual function void Xset_allocate_idX(vmm_data tr, int idx = -1);
   extern function void allocate_scenario(T using = null); 
   extern function void fill_scenario(T using = null); 
   extern function void pre_randomize(); 
   extern virtual task apply(vmm_channel_typed#(T) channel, ref int unsigned n_insts); 
   
   constraint `vmm_scenario_valid_(T) ; 
endclass


class vmm_inject_item_scenario#(type T = vmm_data, string text = "") extends vmm_ss_scenario#(T);
   extern function new(T obj `VMM_DATA_NEW_ARGS);
   extern virtual task apply(vmm_channel_typed#(T) channel, ref int unsigned n_insts);
endclass


class vmm_atomic_scenario#(type T=vmm_data) extends vmm_ss_scenario#(T); 
   int unsigned ATOMIC; 
   constraint atomic_scenario { 
      if (scenario_kind == ATOMIC) { 
         length == 1; 
         repeated == 0; 
      } 
   } 
   
   extern function new(`VMM_DATA_NEW_ARGS); 
   extern virtual function string psdisplay(string prefix = ""); 
   extern function void pre_randomize(); 
   extern virtual task apply(vmm_channel_typed#(T) channel, ref int unsigned n_insts);
endclass

class vmm_scenario_election#(type T=vmm_data, string text = ""); 
   int stream_id; 
   int scenario_id; 
   int unsigned n_scenarios; 
   int unsigned last_selected[$]; 
   int unsigned next_in_set; 
 
   vmm_ss_scenario#(T) scenario_set[$]; 
 
   rand int select; 
 
   constraint vmm_scenario_election_valid { 
      select >= 0; 
      select < n_scenarios; 
   } 
 
   constraint round_robin { 
      select == next_in_set; 
   } 
endclass 

class vmm_scenario_gen_base extends `VMM_XACTOR;

   extern function new(string       name, 
                      string       inst, 
                      int          stream_id = -1
                      `VMM_XACTOR_NEW_ARGS); 

   extern virtual function void replace_scenario(string name, 
                                                 vmm_ss_scenario_base scenario); 
   extern virtual function void register_scenario(string name, 
                                                 vmm_ss_scenario_base scenario); 
   extern virtual function bit scenario_exists(string name); 

   extern virtual function vmm_ss_scenario_base Xget_scenarioX(string name); 
endclass

class vmm_scenario_gen#(type T=vmm_data,string text = "") extends vmm_scenario_gen_base;
   int unsigned stop_after_n_insts; 
   int unsigned stop_after_n_scenarios; 
   vmm_ss_scenario#(T)           scenario_set[$]; 
   protected vmm_ss_scenario#(T) scenario_registry[string]; 
 
   typedef enum int {GENERATED, 
                     DONE} symbols_e; 
 
   vmm_scenario_election#(T, text) select_scenario; 
 
   //channel_name out_chan; 
   vmm_channel_typed#(T) out_chan; 
 
   protected int scenario_count; 
   protected int inst_count; 

   extern virtual function string psdisplay(string prefix = ""); 
   extern function new(string       inst, 
                      int          stream_id = -1, 
                      vmm_channel_typed#(T) out_chan  = null 
                      `VMM_XACTOR_NEW_ARGS); 

   extern virtual function void replace_scenario(string name, 
                                                 vmm_ss_scenario_base scen); 
   extern virtual function void register_scenario(string name, 
                                                 vmm_ss_scenario_base scen); 
   extern virtual function bit scenario_exists(string name); 

   extern virtual function vmm_ss_scenario_base Xget_scenarioX(string name); 
   extern virtual function void get_all_scenario_names(ref string name[$]);
   extern virtual function void get_names_by_scenario(vmm_ss_scenario_base scenario, 
                                                  ref string name[$]); 
   extern virtual function string get_scenario_name(vmm_ss_scenario#(T) scenario); 
           string s[$]; 
   extern virtual function int get_scenario_index(vmm_ss_scenario_base scenario); 
   extern virtual function bit unregister_scenario(vmm_ss_scenario_base scenario); 
   extern function int unsigned get_n_insts(); 
   extern function int unsigned get_n_scenarios(); 
   extern virtual task inject_obj(T obj); 
   extern virtual task inject(vmm_ss_scenario#(T) scenario);
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); 
   extern virtual protected task main(); 
   
   function vmm_ss_scenario#(T) unregister_scenario_by_name(string name); 
      if(name == "") begin 
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
         return null; 
      end 
      if(!this.scenario_registry.exists(name)) begin 
         `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the scenario registry", name)); 
         return null; 
      end 
      else begin 
         $cast(unregister_scenario_by_name, this.scenario_registry[name]); 
         foreach(this.scenario_set[i]) begin 
            vmm_ss_scenario_base scn = this.scenario_registry[name];
            if(this.scenario_set[i] == scn) begin 
               this.scenario_set.delete(i); 
               break; 
            end 
         end 
         this.scenario_registry.delete(name); 
      end 
   endfunction: unregister_scenario_by_name 

   function vmm_ss_scenario#(T) get_scenario(string name); 
      if(name == "") begin 
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
         return null; 
      end 
      if(!this.scenario_registry.exists(name)) begin 
         `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the scenario registry", name)); 
         return null; 
      end 

      $cast(get_scenario, this.scenario_registry[name]); 
      if(get_scenario == null) 
         `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario associated with it in the scenario registry", name)); 

   endfunction: get_scenario 
endclass

class vmm_scenario_gen_callbacks#(type T = vmm_data, string text = "" ) extends vmm_xactor_callbacks; 
   extern virtual task pre_scenario_randomize(vmm_scenario_gen #(T, text) gen, 
                                             ref vmm_ss_scenario #(T) scenario);
   extern virtual task post_scenario_gen(vmm_scenario_gen #(T, text) gen, 
                                        vmm_ss_scenario #(T) scenario, 
                                        ref bit                    dropped); 
endclass


//---------------------------------------------------------------------
// vmm_xactor_iter
//
class vmm_xactor_iter;
  static `VMM_LOG log = new("vmm_xactor_iter", "class");

  string name;
  string inst;

`ifdef NO_STATIC_METHODS
  local static vmm_xactor _vmm_xactor = null;
`endif
  local int idx;

  extern function new(string  name = "",
                      string  inst = "");
  extern function vmm_xactor first();
  extern function vmm_xactor next();
  extern function vmm_xactor xactor();

  extern protected function void move_iterator();
endclass


//---------------------------------------------------------------------
// vmm_ms_scenario_gen
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_gen_callbacks extends vmm_xactor_callbacks;
   virtual task pre_scenario_randomize(vmm_ms_scenario_gen gen,
                                       ref vmm_ms_scenario scenario);
   endtask

   virtual task post_scenario_gen(vmm_ms_scenario_gen gen,
                                  vmm_ms_scenario     scenario,
                                  ref bit             dropped);
   endtask
endclass: vmm_ms_scenario_gen_callbacks


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_ms_scenario_gen extends `VMM_XACTOR;
    local vmm_channel channel_registry[string];
    local vmm_ms_scenario mss_registry[string];
    local vmm_ms_scenario_gen mssg_registry[string];

    int unsigned stop_after_n_insts;
    int unsigned stop_after_n_scenarios;

    typedef enum int {GENERATED, DONE} symbols_e;

    vmm_ms_scenario_election select_scenario;
    vmm_ms_scenario scenario_set[$];

    protected int scenario_count;
    protected int inst_count;

    extern function new(string inst, int stream_id=-1
                        `VMM_XACTOR_NEW_ARGS);
    extern virtual function string psdisplay(string prefix = "");

    extern function int unsigned get_n_insts();
    extern function int unsigned get_n_scenarios();
    extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

    extern virtual function void register_channel(string name,
                                                  vmm_channel chan);
    extern virtual function bit channel_exists(string name);
    extern virtual function void replace_channel(string name,
                                                 vmm_channel chan);
    extern virtual function void get_all_channel_names(ref string name[$]);
    extern virtual function void get_names_by_channel(vmm_channel chan,
                                                      ref string name[$]);
    extern virtual function string get_channel_name(vmm_channel chan);
    extern virtual function bit unregister_channel(vmm_channel chan);
    extern virtual function vmm_channel unregister_channel_by_name(string name);
    extern virtual function vmm_channel get_channel(string name);

    extern virtual function void register_ms_scenario(string name,
                                                      vmm_ms_scenario scenario);
    extern virtual function bit ms_scenario_exists(string name);
    extern virtual function void replace_ms_scenario(string name,
                                                     vmm_ms_scenario scenario);
    extern virtual function void get_all_ms_scenario_names(ref string name[$]);
    extern virtual function void get_names_by_ms_scenario(vmm_ms_scenario scenario,
                                                          ref string name[$]);
    extern virtual function string get_ms_scenario_name(vmm_ms_scenario scenario);
    extern virtual function int get_ms_scenario_index(vmm_ms_scenario scenario);
    extern virtual function bit unregister_ms_scenario(vmm_ms_scenario scenario);
    extern virtual function vmm_ms_scenario unregister_ms_scenario_by_name(string name);
    extern virtual function vmm_ms_scenario get_ms_scenario(string name);

    extern virtual function void register_ms_scenario_gen(string name,
                                                          vmm_ms_scenario_gen scenario_gen);
    extern virtual function bit ms_scenario_gen_exists(string name);
    extern virtual function void replace_ms_scenario_gen(string name,
                                                         vmm_ms_scenario_gen scenario_gen);
    extern virtual function void get_all_ms_scenario_gen_names(ref string name[$]);
    extern virtual function void get_names_by_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen,
                                                              ref string name[$]);
    extern virtual function string get_ms_scenario_gen_name(vmm_ms_scenario_gen scenario_gen);
    extern virtual function bit unregister_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen);
    extern virtual function vmm_ms_scenario_gen unregister_ms_scenario_gen_by_name(string name);
    extern virtual function vmm_ms_scenario_gen get_ms_scenario_gen(string name);

    extern virtual protected task main();
endclass: vmm_ms_scenario_gen


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_broadcast extends `VMM_XACTOR;

   typedef enum {AFAP = 1,
                 ALAP = 2
                 } bcast_mode_e;

   local vmm_channel in_chan;

   local int n_out_chans;
   local bit dflt_use_refs;
   local int mode;

   local bit          use_refs[$];
   local bit          is_on[$];
   local vmm_channel  out_chans[$];

   local event new_cycle;

   extern function new(string      name,
                       string      inst,
                       vmm_channel source,
                       bit         use_references = 1,
                       int         mode           = AFAP
                       `VMM_XACTOR_NEW_ARGS);
   extern virtual function string psdisplay(string prefix = "");

   extern virtual task broadcast_mode(bcast_mode_e mode);
   extern virtual function int new_output(vmm_channel channel,
                                          logic use_references = 1'bx);
   extern virtual function void bcast_on(int unsigned output_id);
   extern virtual function void bcast_off(int unsigned output_id);
   extern virtual protected function bit add_to_output(int unsigned decision_id,
                                                       int unsigned output_id,
                                                       vmm_channel       channel,
                                                       vmm_data          obj);
   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();

   extern local function void bcast_on_off(int channel_id,
                                           int on_off);
   extern virtual task bcast_to_output(int channel_id,
                                       int on_off);
   extern local task broadcast();
   extern local task sink_if_outs();
endclass : vmm_broadcast


//---------------------------------------------------------------------
// vmm_scheduler
//

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scheduler_election;
   int          instance_id;
   int unsigned election_id;

   int unsigned      n_sources;
   vmm_channel       sources[$];
   int unsigned      ids[$];
   int unsigned      id_history[$];
   vmm_data          obj_history[$];
   int unsigned      next_idx;

   rand int unsigned source_idx;
   rand int unsigned obj_offset;

   constraint vmm_scheduler_election_valid {
      obj_offset == 0;
      source_idx >= 0;
      source_idx < n_sources;
   }

   constraint default_round_robin {
      source_idx == next_idx;
   }
endclass


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_scheduler extends `VMM_XACTOR;

   vmm_scheduler_election randomized_sched;

   protected vmm_channel out_chan;

   local vmm_channel       sources[$];
   local int               is_on[$];
   local int               instance_id;
   local int               election_count;
   local event             next_cycle;

   extern function new(string       name,
                       string       inst,
                       vmm_channel  destination,
                       int          instance_id = -1
                       `VMM_XACTOR_NEW_ARGS);
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function int new_source(vmm_channel channel);
   extern virtual task sched_from_input(int channel_id,
                                        int on_off);
   extern virtual protected task schedule(output vmm_data     obj,
                                          input  vmm_channel  sources[$],
                                          input  int unsigned input_ids[$]);
   extern virtual protected task get_object(output vmm_data     obj,
                                            input  vmm_channel  source,
                                            input  int unsigned input_id,
                                            input  int          offset);
   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();

   extern local task schedule_cycle();
endclass


//---------------------------------------------------------------------
// XVC
//

typedef class xvc_xactor;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_action extends `VMM_DATA;
   local string name;

   vmm_xactor_callbacks callbacks[];

   extern function new(string name,
                       vmm_log log);

   extern function string get_name();

   extern virtual function xvc_action parse(string argv[]);
   extern virtual task execute(vmm_channel exec_chan,
                               xvc_xactor  xvc);

   extern virtual function string psdisplay(string prefix = "");
   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);

   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);
   extern virtual protected function void copy_data(vmm_data to);

   extern virtual function bit compare(input  vmm_data to,
                                       output string   diff,
                                       input  int      kind = -1);

   extern virtual function int unsigned byte_size(int kind = -1);
   extern virtual function int unsigned max_byte_size(int kind = -1);
   extern virtual function int unsigned byte_pack(ref logic [7:0]    bytes[],
                                                  input int unsigned offset = 0,
                                                  input int          kind   = -1);
   extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                    input int unsigned    offset = 0,
                                                    input int             len    = -1,
                                                    input int             kind   = -1);
endclass: xvc_action

`vmm_channel(xvc_action)


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_xactor extends `VMM_XACTOR;

   `VMM_LOG trace;

   xvc_action_channel action_chan;
   xvc_action_channel interrupt_chan;

   protected vmm_channel exec_chan;
   protected vmm_xactor  xactors[];

   local xvc_action known_actions[$];
   local xvc_action idle;

   local bit interrupt;
   local bit interrupted;
   local event interrupted_event;
   local event rte;
   local xvc_action executing;
   local xvc_action suspended;

   extern function new(string             name,
                       string             inst,
                       int                stream_id = -1,
                       xvc_action_channel action_chan = null,
                       xvc_action_channel interrupt_chan = null
                       `VMM_XACTOR_NEW_ARGS);

   extern function void add_action(xvc_action action);
   extern function xvc_action parse(string argv[]);

   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

   extern virtual function void xactor_status(string prefix = "");

   extern virtual task main();

   extern task wait_if_interrupted();

   extern local task execute_actions();
   extern local task execute_interruptions();
   extern local task execute_action(xvc_action_channel chan,
                                    string             descr);

   extern virtual function void save_rng_state();
   extern virtual function void restore_rng_state();
endclass: xvc_xactor


`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class xvc_manager;

   `VMM_LOG    log;
   `VMM_LOG    trace;

   `VMM_NOTIFY notify;

   protected xvc_xactor xvcQ[$];

   extern function new(string inst = "Main");

   extern function bit add_xvc(xvc_xactor xvc);
   extern function bit remove_xvc(xvc_xactor xvc);

   extern function bit split(string     command,
                             ref string argv[]);

endclass: xvc_manager


//------------------------------------------------------------
// vmm_test
//
typedef class vmm_timeline;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_test
`ifdef VMM_TEST_BASE
   extends `VMM_TEST_BASE
`endif
;
   `vmm_typename(vmm_test)
   bit selected;
   local bit config_enable;
   local bit config_called;
   local string name;
   local string doc;
   vmm_log log;

   static vmm_test_registry registry = new;

   extern function                        new(string       name = "", 
                                              string        doc = "", 
                                              vmm_object parent = null);
   extern virtual function void    set_config();
   extern virtual function string     get_doc();
   extern virtual function string    get_name();
   extern function bit        has_config_done();
   extern virtual task                    run(vmm_env env);

   extern function void    Xset_log_instanceX(string inst);
endclass

//------------------------------------------------------------
// vmm_test_registry
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_test_registry;
   static local vmm_opts _vmm_opts = new();

   local static vmm_test registry[string];
   local static vmm_log log = new("vmm_test_registry", "class");
   local static int width = 1;

   extern `VMM_STATIC_M task run(vmm_env env);
   extern `VMM_STATIC_M function void list();

   extern /*local*/ `VMM_STATIC_M function void Xregister_testX(vmm_test tst);
   extern local `VMM_STATIC_M function void display_known_tests(ref string msg[$],
                                                                input bit fatal);
endclass

//------------------------------------------------------------
// vmm_path_match
//
`ifndef VMM_PATH_MATCH
`define VMM_PATH_MATCH vmm_path_match
`endif

typedef class `VMM_PATH_MATCH;

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif

class vmm_path_match;
   extern  static function `vmm_path_compiled compile_path(vmm_log log, vmm_object scope = null, 
                                                          string name = "", string space = "");
   extern  static function `vmm_path_regexp compile_pattern(string pattern, vmm_log log);
   extern  static function bit match(`vmm_path_compiled name, `vmm_path_regexp pattern);
endclass: vmm_path_match

//------------------------------------------------------------
// vmm_phase_def
//
typedef class vmm_unit;
typedef class vmm_timeline;

// Timeline phase definitions
virtual class vmm_phase_def;
   pure virtual function string        get_typename();
   pure virtual function bit      is_function_phase();
   pure virtual function bit          is_task_phase();
   pure virtual function void    run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   pure virtual task                 run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
endclass

// New Timeline phase definition class, if extended to use will execute parent 
// phase before child phase
virtual class vmm_topdown_function_phase_def #(type T = vmm_object) extends vmm_phase_def;
   `vmm_typename(vmm_topdown_function_phase_def);
   extern virtual function bit    is_function_phase();
   extern virtual function bit        is_task_phase();
   extern virtual function void  run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   extern virtual task               run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   pure virtual function void     do_function_phase(T obj);
endclass

/* New Timeline phase definition class , if extended to use will execute child 
   phases before parent phases */
virtual class vmm_bottomup_function_phase_def #(type T = vmm_object) extends vmm_phase_def;
   `vmm_typename(vmm_bottomup_function_phase_def);
   extern virtual function bit    is_function_phase();
   extern virtual function bit        is_task_phase();
   extern virtual function void  run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   extern virtual task               run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   pure virtual function void     do_function_phase(T obj);
endclass:vmm_bottomup_function_phase_def

virtual class vmm_fork_task_phase_def #(type T = vmm_object) extends vmm_phase_def;
   `vmm_typename(vmm_fork_task_phase_def);
   extern virtual function bit    is_function_phase();
   extern virtual function bit        is_task_phase();
   extern virtual function void  run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   extern virtual task               run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   pure virtual task                  do_task_phase(T obj);
endclass:vmm_fork_task_phase_def

virtual class vmm_xactor_phase_def #(type T = vmm_xactor) extends vmm_phase_def;
   `vmm_typename(vmm_xactor_phase_def);
   string name,inst;
   extern function                              new(string name = "/./",
                                                    string inst = "/./");
   extern virtual function bit    is_function_phase();
   extern virtual function bit        is_task_phase();
   extern virtual function void  run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   extern virtual task               run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   pure virtual function void         do_function_phase(T obj);
endclass:vmm_xactor_phase_def

/* Null timeline phase definition class with empty run_function_phase() */
virtual class vmm_null_phase_def #(type T = vmm_object) extends vmm_phase_def;
   `vmm_typename(vmm_null_phase_def);
   extern virtual function bit    is_function_phase();
   extern virtual function bit        is_task_phase();
   extern virtual function void  run_function_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
   extern virtual task               run_task_phase(string     name, 
                                                    vmm_object obj, 
                                                    vmm_log    log);
endclass:vmm_null_phase_def
//------------------------------------------------------------
// vmm_unit
//
typedef class vmm_simulation;
typedef class vmm_timeline;
typedef class vmm_phase_def;

/* vmm_unit class is base class for structural components ,
   such as transactors,transaction-level models and generators */
virtual class vmm_unit extends vmm_object;
   `vmm_typename(vmm_unit)
   vmm_log log;

   protected bit enable_unit;
   bit reset_ph_done;
  
   //track all overridden definitions
   vmm_phase_def override_phase_defs[string];

   //phase executed notification
   bit phase_executed[string];
   vmm_consensus vote;
   local vmm_voter voter;
   

   extern function                                       new(string        name, 
                                                             string        inst ,
                                                             vmm_object    parent = null);
   extern function vmm_timeline                 get_timeline();
   extern virtual function vmm_phase_def      override_phase(string        name, 
                                                             vmm_phase_def def);
   extern function bit                       is_unit_enabled();
   extern local function void             disable_child_unit(vmm_object    obj);
   extern function void                         disable_unit();
   extern function void                    set_parent_object(vmm_object parent);
   extern virtual function void                      consent(string why="No reason specified");
   extern virtual function void                       oppose(string why="No reason specified");

   //phase methods
   extern virtual function void                     build_ph();
   extern virtual function void                 configure_ph();
   extern virtual function void                   connect_ph();
   extern virtual function void              start_of_sim_ph();
   extern virtual task                           disabled_ph();
   extern virtual task                              reset_ph();
   extern virtual task                           training_ph();
   extern virtual task                         config_dut_ph();
   extern virtual task                              start_ph();
   extern virtual function void             start_of_test_ph();
   extern virtual task                                run_ph();
   extern virtual task                           shutdown_ph();
   extern virtual task                            cleanup_ph();
   extern virtual function void                    report_ph();
   extern virtual function void                  destruct_ph();
endclass:vmm_unit

//
class vmm_unit_buildph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_buildph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.build_ph();
   endfunction:do_function_phase
endclass:vmm_unit_buildph_phase_def


//
class vmm_unit_configph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_configph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.configure_ph();
   endfunction:do_function_phase
endclass:vmm_unit_configph_phase_def

//
class vmm_unit_connectph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_connectph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.connect_ph();
   endfunction:do_function_phase
endclass:vmm_unit_connectph_phase_def

//
class vmm_unit_startsimph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_startsimph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.start_of_sim_ph();
   endfunction:do_function_phase
endclass:vmm_unit_startsimph_phase_def

//
class vmm_unit_resetph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_resetph_phase_def)

   task do_task_phase(vmm_unit obj);
      if(obj.is_unit_enabled())
         obj.reset_ph();
      else
         obj.disabled_ph();
   endtask:do_task_phase
endclass:vmm_unit_resetph_phase_def

//
class vmm_unit_trainingph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_trainingph_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.training_ph();
   endtask:do_task_phase
endclass:vmm_unit_trainingph_phase_def

//
class vmm_unit_configdut_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_configdut_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.config_dut_ph();
   endtask:do_task_phase
endclass:vmm_unit_configdut_phase_def

//
class vmm_unit_startph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_startph_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.start_ph();
   endtask:do_task_phase
endclass:vmm_unit_startph_phase_def

//
class vmm_unit_starttestph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_startph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.start_of_test_ph();
   endfunction:do_function_phase
endclass:vmm_unit_starttestph_phase_def

//
class vmm_unit_run_testph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_run_testph_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.run_ph();
   endtask:do_task_phase
endclass:vmm_unit_run_testph_phase_def

//
class vmm_unit_shutdownph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_shutdownph_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.shutdown_ph();
   endtask:do_task_phase
endclass:vmm_unit_shutdownph_phase_def

//
class vmm_unit_cleanupph_phase_def extends vmm_fork_task_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_cleanupph_phase_def)

   task do_task_phase(vmm_unit obj);
      obj.cleanup_ph();
   endtask:do_task_phase
endclass:vmm_unit_cleanupph_phase_def

//
class vmm_unit_reportph_phase_def extends vmm_topdown_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_reportph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.report_ph();
   endfunction:do_function_phase
endclass:vmm_unit_reportph_phase_def

//
class vmm_unit_destructph_phase_def extends vmm_bottomup_function_phase_def #(vmm_unit);
   `vmm_typename(vmm_unit_destructph_phase_def)

   function void do_function_phase(vmm_unit obj);
      obj.destruct_ph();
   endfunction:do_function_phase
endclass:vmm_unit_destructph_phase_def

class vmm_start_xactor_phase_def extends vmm_xactor_phase_def #(vmm_xactor);
   `vmm_typename(vmm_start_xactor_phase_def);

   function new(string name = "/./",string inst = "/./");
      super.new(name,inst);
   endfunction

   function void do_function_phase(T xactor);
	  xactor.start_xactor();
   endfunction:do_function_phase
endclass:vmm_start_xactor_phase_def

class vmm_stop_xactor_phase_def extends vmm_xactor_phase_def #(vmm_xactor);
   `vmm_typename(vmm_stop_xactor_phase_def);

   function new(string name = "/./",string inst = "/./");
      super.new(name,inst);
   endfunction

   function void do_function_phase(T xactor);
	 xactor.stop_xactor();
   endfunction:do_function_phase
endclass:vmm_stop_xactor_phase_def

class vmm_reset_xactor_phase_def extends vmm_xactor_phase_def #(vmm_xactor);
   `vmm_typename(vmm_reset_xactor_phase_def);

   function new(string name = "/./",string inst = "/./");
      super.new(name,inst);
   endfunction

   function void do_function_phase(T xactor);
	  xactor.reset_xactor();
   endfunction:do_function_phase
endclass:vmm_reset_xactor_phase_def

//------------------------------------------------------------
// vmm_phase
//
typedef class vmm_phase_def;

// User-consumable phase descriptor
virtual class vmm_phase extends vmm_object;
   `vmm_typename(vmm_phase)

   event started,completed;
   local bit running;
   local bit phase_done;
   bit abort_done;
   int unsigned abort_count;
   int unsigned skipped_count;
   int unsigned done_count;
   bit timeout_done;

   extern function                          new(string       name, 
                                                vmm_timeline parent = null);
   extern function string              get_name();
   extern function vmm_timeline    get_timeline();
   extern function vmm_phase     previous_phase();
   extern function vmm_phase         next_phase();
   extern /*local*/ function void   set_running();
   extern /*local*/ function void reset_running();
   extern function bit               is_running();
   extern /*local*/ function bit  is_phase_done();
   extern function int                  is_done();
   extern /*local*/ function void    reset_done();
   extern function int               is_aborted();
   extern function int               is_skipped();
endclass

//------------------------------------------------------------
// vmm_rtl_config
//
typedef class vmm_rtl_config;
typedef class vmm_rtl_config_phase_build_cfg_ph_def;
typedef class vmm_rtl_config_phase_get_cfg_ph_def;
typedef class vmm_rtl_config_phase_save_cfg_ph_def;

class vmm_rtl_config_phase_def extends vmm_phase_def;
   `vmm_typename(vmm_rtl_config_phase_def)
   static vmm_log                        log = new("vmm_rtl_config_phase_def", "class");
   vmm_rtl_config                        rtl_cfg;
   vmm_rtl_config_phase_build_cfg_ph_def build_cfg_ph;
   vmm_rtl_config_phase_get_cfg_ph_def   get_cfg_ph;
   vmm_rtl_config_phase_save_cfg_ph_def  save_cfg_ph;

   extern virtual function void run_function_phase(string name, vmm_object obj, vmm_log log);
   extern virtual task          run_task_phase(string name, vmm_object obj, vmm_log log);
   extern virtual function bit  is_function_phase();
   extern virtual function bit  is_task_phase();

endclass:vmm_rtl_config_phase_def

typedef class vmm_rtl_config_file_format;
class vmm_rtl_config extends vmm_object;
  `vmm_typename(vmm_rtl_config)
  typedef      enum {LOAD, SAVE} mode_e;
  static       bit    Xgen_rtl_configX = vmm_opts::get_bit("gen_rtl_config", "Specifies Generation of VMM RTL Configuration");
  static       string XprefixX         = vmm_opts::get_string("rtl_config", "",
                                                    "Specfies VMM RTL Configuration option");
  static       local bit rtl_cfg_space = vmm_object::create_namespace("VMM RTL Config", vmm_object::IN_BY_DEFAULT);
  static       vmm_rtl_config_file_format default_file_fmt;
  protected    vmm_rtl_config_file_format file_fmt;
  vmm_log      log;
  static int   Xfile_ptrX;
  protected    int   Xload_save_doneX;

extern function                                     new(string name = "", 
													  vmm_rtl_config parent = null);
extern         function void                map_to_name(string name);
extern virtual function void            build_config_ph();
extern virtual function void              get_config_ph();
extern virtual function void             save_config_ph();
extern static  function vmm_rtl_config       get_config(vmm_object uobj, 
													  string     fname = "", 
													  int        lineno = 0);
extern virtual protected function void load_save_config(mode_e load_param);

endclass: vmm_rtl_config

virtual class vmm_rtl_config_file_format;
pure virtual function bit fopen(vmm_rtl_config cfg, 
							  string mode, 
							  string fname = "", 
							  int lineno = 0);
pure virtual function bit read_bit(string name, output bit value);
pure virtual function bit read_int(string name, output int value);
pure virtual function bit read_string(string name, output string value);
pure virtual function bit write_bit(string name, bit value);
pure virtual function bit write_int(string name, int value);
pure virtual function bit write_string(string name, string value);
pure virtual function void   fclose();
     extern  virtual protected function string fname(vmm_rtl_config cfg);
endclass




//------------------------------------------------------------
// vmm_timeline
//

//facade callback class
virtual class vmm_timeline_callbacks;
 virtual function void break_on_phase(vmm_timeline tl,string name);
 endfunction:break_on_phase
endclass

typedef class vmm_phase_impl;
class vmm_timeline extends vmm_unit;
   `vmm_typename(vmm_timeline)

   typedef enum {TASK,FUNCTION} METHOD_TYPE;
   local string phases[$];
   local vmm_phase_impl phase_impls[string];
   local int unsigned timeout_for_phases[string];
   local bit do_abort_phase;
   local int current_phase = -1;
   local string running = "";
   local bit set_run_subtimelines_to_end;

   /*protected*/ vmm_timeline_callbacks callbacks[$];

   extern function                                 new(string name = "", 
                                                       string inst = "",
		                                       vmm_object parent = null);
   extern virtual function void       prepend_callback(vmm_timeline_callbacks cb);
   extern virtual function void        append_callback(vmm_timeline_callbacks cb);
   extern virtual function void    unregister_callback(vmm_timeline_callbacks cb);
   extern local function bit     is_stop_for_phase_set(string name);
   extern function vmm_phase                 get_phase(string name);
   extern function string        get_current_phase_name();
   extern function void                 display_phases();
   extern function string           get_previous_phase_name(string          name);
   extern function string               get_next_phase_name(string          name);
   extern function void            step_function_phase(string          name, 
                                                       string          fname ="", 
			                               int             lineno =0);
   extern function void                     abort_phase(string          name, 
                                                       string          fname ="", 
			                               int             lineno =0);
   extern function bit                    insert_phase(string          phase_name, 
                                                       string          before_name, 
			                               vmm_phase_def   def,
			                               string          fname ="",
			                               int             lineno = 0);
   extern function bit                       add_phase(string          name, 
                                                       vmm_phase_def   def);
   extern function bit                     delete_phase(string         phase_name, 
                                                       string          fname ="", 
			                               int             lineno =0);
   extern function bit                     rename_phase(string         old_name, 
                                                        string         new_name, 
			                             	string         fname ="", 
			                             	int            lineno =0);
   extern function void                    jump_to_phase(string         name, 
			                             	string         fname ="", 
			                             	int            lineno =0);
   extern local function void       jump_child_to_phase(string         name, 
				                        vmm_object     obj); 
   extern task                                run_phase(string         name = "$", 
                                                        string         fname ="", 
		                                 	 int           lineno =0);
   extern function void              run_function_phase(string         name);
   extern local task                get_ready_for_phase(string         name, 
                                                        vmm_object     obj);
   extern local task          get_child_ready_for_phase(string         name, 
                                                        vmm_object     obj);
   extern local task                     run_phase_impl(string         name, 
                                                        vmm_phase_impl impl);
   extern function void                  reset_to_phase(string         name, 
                                                        string         fname ="", 
			                             	int            lineno =0);
   extern local function void   reset_children_to_phase(string         name, 
                                                        vmm_object     obj);
   extern local function void         enable_child_unit(vmm_object     obj,
                                                        int unsigned   ph_index);
   extern function bit               task_phase_timeout(string         name, 
                                                        int unsigned   delta, 
			                             	string         fname ="", 
			                             	int            lineno =0);
   extern local function METHOD_TYPE get_phase_method_type(string      name);
   extern local function bit       insert_phase_internal(string        phase_name, 
                                                         string        before_name, 
				                         vmm_phase_def def,
				                         string        fname ="",
				                         int           lineno = 0);
   extern local task                          delay_task(string        name,
                                                         int unsigned  delay,
			                               	 ref bit       running_phase_thread_done);
   extern /*local*/ function int get_current_phase_index();
   extern /*local*/ function int         get_phase_index(string        name);
   extern local task   wait_child_object_to_finish_phase(string        name, 
                                                         vmm_object    obj);
   extern local task               flush_child_timelines(vmm_object    obj);
   extern local function void   set_abort_done_for_child(string name,
                                                         vmm_object obj);
   extern local function void set_timeout_done_for_child(string name,
                                                         vmm_object obj);
endclass:vmm_timeline

//------------------------------------------------------------
// vmm_simulation
//
// Top-level simulation timeline
class vmm_simulation extends vmm_unit;
   `vmm_typename(vmm_simulation)
   local static vmm_simulation me        = new();
   local static vmm_log log    = new("vmm_simulation","class");
   local static vmm_timeline   pre_test;
   local static vmm_timeline   top_test;
   local static vmm_timeline   post_test;
   local static bit allow_new_ph;
   local static int width = 1;
   //static local vmm_opts _vmm_opts = new();
   // Need test registry, run-time selection, etc...
   static local vmm_test tests[string];
   static /*local*/ vmm_object Xenv_rootsX[$];

   extern local function new();
   extern `VMM_STATIC_M function vmm_simulation          get_sim();
   extern `VMM_STATIC_M function vmm_timeline            get_pre_timeline();
   extern `VMM_STATIC_M function vmm_timeline            get_top_timeline();
   extern `VMM_STATIC_M function vmm_timeline            get_post_timeline();
   extern `VMM_STATIC_M function bit           insert_test_phase(string          phase_name,
                                                                 string          before_name,
                                                                 vmm_phase_def   def);
   extern `VMM_STATIC_M function void           allow_new_phases(bit             allow = 1);
   extern `VMM_STATIC_M task                  run_pre_test_phase(string          name);
   extern `VMM_STATIC_M function void             display_phases();
   extern `VMM_STATIC_M task                           run_tests();
   extern `VMM_STATIC_M function void            Xregister_testX(vmm_test        tst);
   extern `VMM_STATIC_M function void        display_known_tests(ref string      msg[$],
                                                                 input bit       fatal);
   extern `VMM_STATIC_M function void                       list();
   extern `VMM_STATIC_M function void        get_tests_to_run();
   extern `VMM_STATIC_M function int         collect_root_objects();
endclass

/// TO DO
    
//------------------------------------------------------------
// vmm_object_iter
//
class vmm_object_iter;
  static local vmm_log log = new("vmm_object_iter", "class");

  local string name;
  local string _space;
  local vmm_object _root;

  // string containing the name in the form of a regular expression.
  //local string _regex;
  local `vmm_path_regexp _regex;
  
  //local queue to store all vmm_object in the order as required by BSF
  local vmm_object _bfs_obj_q[$];
  
  //local queue to store all the roots. In case a null root is specified all roots are considered.
  local vmm_object _root_q[$];
  local bit _null_root = 0;

  extern function new(vmm_object root = null,
		      string  name = "",
		      string space = ""
					  );
  extern function vmm_object first();
  extern function vmm_object next();
endclass


//------------------------------------------------------------
// vmm_rw*
//


class vmm_rw;
   typedef enum {
      READ,
      WRITE,
      EXPECT
   } kind_e;

   typedef enum {
      IS_OK,
      ERROR,
      RETRY,
      TIMEOUT,
      HAS_X
   } status_e;
endclass: vmm_rw


class vmm_rw_access extends `VMM_DATA;
   static vmm_log log = new("vmm_rw_access", "class");

   rand vmm_rw::kind_e kind;

   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] addr;
   rand logic [`VMM_RW_DATA_WIDTH-1:0] data;
   rand int                            n_bits = `VMM_RW_DATA_WIDTH;
   local string                        fname = "";
   local int                           lineno = 0;

   vmm_rw::status_e status;

   constraint valid_vmm_rw_access {
      n_bits > 0;
      n_bits < `VMM_RW_DATA_WIDTH;
   }

   extern function new(
   `ifdef VMM_12_UNDERPIN_STDLIB
      vmm_object parent, string name
   `endif
   );
   extern virtual function string psdisplay(string prefix = "");
endclass: vmm_rw_access
`vmm_channel(vmm_rw_access)


class vmm_rw_burst extends vmm_rw_access;
   rand int unsigned n_beats;
   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] incr_addr;
   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] max_addr;
   rand logic [`VMM_RW_DATA_WIDTH-1:0] data[];
        vmm_data                       user_data;

   constraint vmm_rw_burst_valid {
      n_beats > 0;
      max_addr >= addr;
      if (kind == vmm_rw::WRITE || kind == vmm_rw::EXPECT) data.size() == n_beats;
      else data.size() == 0;
   }

   constraint reasonable {
      n_beats <= 1024;
      incr_addr inside {0, 1, 2, 4, 8, 16, 32};
   }

   constraint linear {
      incr_addr == 1;
      max_addr == addr + n_beats - 1;
   }

   constraint fifo {
      incr_addr == 0;
      max_addr == addr;
   }

   constraint wrap {
      incr_addr > 0;
      max_addr < addr + (n_beats - 1)* incr_addr;
   }

   extern function new(
  `ifdef VMM_12_UNDERPIN_STDLIB
      vmm_object parent, string name
   `endif
   );
endclass: vmm_rw_burst


typedef class vmm_rw_xactor;
class vmm_rw_xactor_callbacks extends vmm_xactor_callbacks;
   virtual task pre_single(vmm_rw_xactor xactor,
                           vmm_rw_access tr);
   endtask

   virtual task pre_burst(vmm_rw_xactor xactor,
                          vmm_rw_burst  tr);
   endtask

   virtual task post_single(vmm_rw_xactor xactor,
                            vmm_rw_access tr);
   endtask

   virtual task post_burst(vmm_rw_xactor xactor,
                           vmm_rw_burst  tr);
   endtask
endclass: vmm_rw_xactor_callbacks


class vmm_rw_xactor extends `VMM_XACTOR;
   typedef enum {BURST_DONE = 99990,
                 SINGLE_DONE} notifications_e;

   vmm_rw_access_channel exec_chan;

   extern function new(string name,
                       string inst,
                       int    stream_id = -1,
                       vmm_rw_access_channel exec_chan = null);

   extern protected virtual task execute_single(vmm_rw_access tr);
   extern protected virtual task execute_burst(vmm_rw_burst tr);

   extern protected virtual task main();
   extern function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
endclass: vmm_rw_xactor



//------------------------------------------------------------
// includes
//
`include "std_lib/vmm_opts.sv"
`include "std_lib/vmm_log.sv"
`include "std_lib/vmm_notify.sv"
`include "std_lib/vmm_data.sv"
`include "std_lib/vmm_scenario.sv"
`include "std_lib/vmm_scenario_gen.sv"
`include "std_lib/vmm_channel.sv"
`include "std_lib/vmm_consensus.sv"
`include "std_lib/vmm_subenv.sv"
`include "std_lib/vmm_env.sv"
`include "std_lib/vmm_xactor.sv"
`include "std_lib/vmm_broadcast.sv"
`include "std_lib/vmm_scheduler.sv"
`include "std_lib/vmm_ms_scenario_gen.sv"
`include "std_lib/xvc_action.sv"
`include "std_lib/xvc_xactor.sv"
`include "std_lib/xvc_manager.sv"
`ifdef VMM_XVC_MANAGER
`include "std_lib/vmm_xvc_manager.sv"
`endif
`include "std_lib/vmm_test.sv"
`include "std_lib/vmm_path_match.sv"
`include "std_lib/vmm_object_iter.sv"
`include "std_lib/vmm_phasing.sv"
`include "std_lib/vmm_unit.sv"
`include "std_lib/vmm_rtl_config.sv"
`include "std_lib/vmm_timeline.sv"
`include "std_lib/vmm_simulation.sv"
`include "std_lib/vmm_config_macros.sv"
`include "std_lib/vmm_factory.sv"
`include "std_lib/vmm_rw.sv"

`ifdef VMM_IN_PACKAGE
endpackage: vmm_std_lib
`endif

`endif // VMM__SV

`ifdef VMM_IN_PACKAGE
import vmm_std_lib::*;
`endif

//
// end of VMM Classes declarartion
//---------------------------------------------------------------------
