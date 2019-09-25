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
  
function vmm_tr_stream::new(string stream_name,
                            string msg_name,
                            type_e typ=PARENT,
                            vmm_debug::verbosity_e verbosity=vmm_debug::VERBOSE_SEV);
   this.stream_name = (stream_name != "") ? map_name(stream_name) : "GlobalStream";
   this.msg_name = (msg_name != "") ? map_name(msg_name) : "GlobalMsg";
   this.typ = typ;
   this.verbosity = verbosity;
   this.status = UNDEF;
   this.activated = (vmm_debug::global_verbosity != vmm_debug::UNDEF_SEV) ? 1 : 0;
endfunction bit is_set;

function bit vmm_tr_stream::is_active();
   return activated;
endfunction

 // ensure there no unsupported character in msg to be recorded
function string vmm_tr_stream::map_name(string obj_hier_name);
   string result;
   result = obj_hier_name;
   foreach(result[i]) if (!( (result[i]>="a" && result[i]<="z") ||
                             (result[i]>="A" && result[i]<="Z") ||
                             (result[i]>="0" && result[i]<="9") ||
                              result[i]=="_"       
                           )
                         ) result[i] = "_";
   return result;
endfunction
    
function vmm_tr_stream vmm_tr_record::open_stream(string stream_name,
                                                        string msg_name,
                                                        vmm_debug::verbosity_e verbosity=vmm_debug::VERBOSE_SEV);
`ifdef VMM_TR_RECORD
   vmm_tr_stream handle = new(stream_name, 
                              msg_name, 
                              vmm_tr_stream::PARENT, 
                              verbosity);
   return handle;
`endif
endfunction

function vmm_tr_stream vmm_tr_record::open_sub_stream(vmm_tr_stream top,
                                                            string msg_name_suffix,
                                                            vmm_debug::verbosity_e verbosity=vmm_debug::VERBOSE_SEV);
`ifdef VMM_TR_RECORD
   if(top != null) begin 
      vmm_tr_stream handle = new(top.stream_name, 
                                 $psprintf("%s.%s", top.msg_name, msg_name_suffix), 
                                 vmm_tr_stream::CHILD, 
                                 verbosity);
      return handle;
   end
   else
      return null;
`endif
endfunction

function int vmm_tr_record::tblog(vmm_tr_stream top, 
                                         string header, 
                                         string body);
`ifdef VMM_TR_RECORD
   if(top==null)
      return 0;
   if(top.is_active() && (vmm_debug::global_verbosity >= top.verbosity)) begin
      string str, msg;
      str = $psprintf("%s.%s", top.stream_name, top.msg_name);
      msg = $psprintf("%s.%s", header, body);
      $tblog(0, msg, str);
      return 1;
   end
   return 0;
`endif
endfunction

function int vmm_tr_record::start_tr(vmm_tr_stream top, 
                                             string header, 
                                             string body);
`ifdef VMM_TR_RECORD
   if(top==null)
      return 0;
   if(top.is_active() && (vmm_debug::global_verbosity >= top.verbosity)) begin
      if(top.status!=vmm_tr_stream::STARTED)
         if(top.typ==vmm_tr_stream::PARENT)
            $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
              _vcs_msglog::NORMAL, header, body, _vcs_msglog::START);
         else
            $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
                 _vcs_msglog::TRACE, header, body, _vcs_msglog::START);
      else
         if(top.typ==vmm_tr_stream::PARENT)
            $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
                 _vcs_msglog::NORMAL, header, body, _vcs_msglog::XTEND);
         else
            $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
                 _vcs_msglog::TRACE, header, body, _vcs_msglog::XTEND);
      top.status = vmm_tr_stream::STARTED;
      return 1;
   end
   return 0;
`endif
endfunction

function int vmm_tr_record::extend_tr(vmm_tr_stream top, 
                                             string header, 
                                             string body);
`ifdef VMM_TR_RECORD
   if(top==null)
      return 0;
   if(top.is_active() && (vmm_debug::global_verbosity >= top.verbosity)) begin
      if(top.typ==vmm_tr_stream::PARENT)
         $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
              _vcs_msglog::NORMAL, header, body, _vcs_msglog::XTEND);
      else
         $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
              _vcs_msglog::TRACE, header, body, _vcs_msglog::XTEND);
      top.status = vmm_tr_stream::STARTED;
      return 1;
   end
   return 0;
`endif
endfunction
     
function int vmm_tr_record::end_tr(vmm_tr_stream top);
`ifdef VMM_TR_RECORD
   if(top==null)
      return 0;
   if(top.is_active() && vmm_debug::global_verbosity >= top.verbosity) begin
      if(top.status == vmm_tr_stream::STARTED || top.status == vmm_tr_stream::EXTENDED) begin
         if(top.typ==vmm_tr_stream::PARENT)
           $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
                   _vcs_msglog::NORMAL, _vcs_msglog::FINISH);
         else
           $msglog(top.stream_name, _vcs_msglog::XACTION, top.msg_name,
                   _vcs_msglog::TRACE, _vcs_msglog::FINISH);
         top.status = vmm_tr_stream::FINISHED;
         return 1;
      end
   end
   return 0;
`endif
endfunction
  
function void vmm_tr_record::close_stream(vmm_tr_stream top);
`ifdef VMM_TR_RECORD
   top=null;
`endif
endfunction
  
