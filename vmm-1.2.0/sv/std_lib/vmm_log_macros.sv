

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


