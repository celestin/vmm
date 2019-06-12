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


`define VMM_FILE_MESSAGE(msg, fname, lineno) \
begin \
   string txt; \
   if (fname != "") begin \
     txt = {`"@file `", fname}; \
     if (lineno != 0) begin \
       txt = {`" `", txt, `":`", `vmm_sformatf(`"%0d`", lineno)}; \
     end  \
   end \

`define VMM_FATAL(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_fatal(log, {msg, txt}); \
end

`define VMM_ERROR(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_error(log, {msg, txt}); \
end

`define VMM_WARN(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_warning(log, {msg, txt}); \
end

`define VMM_NOTE(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_note(log, {msg, txt}); \
end

`define VMM_TRACE(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_trace(log, {msg, txt}); \
end

`define VMM_DEBUG(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_trace(log, {msg, txt}); \
end

`define VMM_VERBOSE(msg, fname, lineno) \
   `VMM_FILE_MESSAGE(msg, fname, lineno) \
   `vmm_verbose(log, {msg, txt}); \
end


`define vmm_warning_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_warning(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV, fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_error_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_error(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_fatal_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_fatal(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV, fname, lineno)) begin \
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

`define vmm_trace_FL(log, msg)
`define vmm_debug_FL(log, msg)
`define vmm_verbose_FL(log, msg)
`define vmm_note_FL(log, msg)
`define vmm_report_FL(log, msg)
`define vmm_command_FL(log, msg)
`define vmm_protocol_FL(log, msg)
`define vmm_transaction_FL(log, msg)
`define vmm_cycle_FL(log, msg)
`define vmm_user_FL(n, log, msg)

`else

`define vmm_trace_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_trace(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV, fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_debug_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_debug(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV, fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

     
`define vmm_verbose_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_verbose(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV, fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::DEBUG_TYP, vmm_log::VERBOSE_SEV)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_note_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_note(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::NOTE_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::NOTE_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_report_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_report(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::REPORT_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::REPORT_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_command_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_command(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::COMMAND_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::COMMAND_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_protocol_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_protocol(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::PROTOCOL_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::PROTOCOL_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_transaction_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_transaction(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::TRANSACTION_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::TRANSACTION_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_cycle_FL(log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_cycle(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::CYCLE_TYP, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::CYCLE_TYP)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define vmm_user_FL(n, log, msg)  \
   if (fname == "" || lineno == 0) begin \
     `vmm_user(log, msg); \
   end else \
   do \
      /* synopsys translate_off */ \
`ifdef VMM_LOG_FORMAT_FILE_LINE \
      if (log.start_msg(vmm_log::USER_TYP_``n, , fname, lineno)) begin \
`else \
      if (log.start_msg(vmm_log::USER_TYP_``n)) begin \
`endif \
	 void'(log.text(msg)); \
	 log.end_msg(); \
      end \
      /* synopsys translate_on */ \
   while(0)

`endif // VMM_NULL_LOG_MACROS
