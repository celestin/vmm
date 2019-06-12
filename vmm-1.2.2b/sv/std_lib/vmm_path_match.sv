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

//-----------
// public
//-----------
  function `vmm_path_compiled vmm_path_match::compile_path (vmm_log log, vmm_object scope = null, string name = "", string space = "");
    string path_str = "";
    if((scope == null) && (name != "")) begin
       `ifdef VMM_REGEX_DEBUG
       `vmm_warning(log,"vmm_object instance is null. Attempting to match absolute path");
       `endif
       path_str = {name};
    end
    else if((scope != null) && (name == "")) begin
       path_str = {scope.get_object_hiername(null, space)};
    end
    else if((scope != null) && (name != "")) begin
       path_str = {scope.get_object_hiername(null, space),":",name};
    end
    else begin
       `vmm_warning(log,"Both vmm_object instance and string name are null. Returning null results");
    end
    return path_str;
  endfunction:compile_path

  function `vmm_path_regexp vmm_path_match::compile_pattern(string pattern, vmm_log log);
     string regex;
     bit regex_not_found = 1;
     bit first_char_regex = 0;
     
     // The input string is a match-pattern
     if (pattern[0] == "@") begin
        pattern = pattern.substr(1, pattern.len()-1);
        for (int i=0; i<pattern.len(); i++) begin
	       string one_char ;
		   `ifndef MACRO_CAST
	       one_char = `_TO_CAST_TO_STRING(pattern.getc(i));
		   `else
		   $cast(one_char,pattern.getc(i));
		   `endif
		   
	       if ((pattern.getc(0) == ".")|| 
	           (pattern.getc(0) == "*")||
	           (pattern.getc(0) == "?")||
	           (pattern.getc(0) == "%")
	          ) begin
	         first_char_regex = 1;
	       end
	       
           if (one_char == ".")begin
	          regex_not_found = 0;
	          regex = {regex, "[^:]"};
	       end
           else if (one_char == "*")begin 
	          regex_not_found = 0;
	          regex = {regex, "[^:]*"};
	       end
           else if (one_char == "?")begin
	          regex_not_found = 0;
	          regex = {regex, "[^:]?"};
	       end
           else if (one_char == "%")begin
	          regex_not_found = 0;
	          regex = {regex, "(([^:]+)?[:]+)*"};
	       end
           else if (one_char == "^")begin
	          regex_not_found = 0;
	          regex = {regex, "\^"};
	       end
           else if (one_char == "$")begin
	          regex_not_found = 0;
	          regex = {regex, "\$"};
	       end
           else if (one_char == "+")begin
	          regex = {regex, "\+"};
	          regex_not_found = 0;
	       end
           else if (one_char == "\\")begin
	          regex_not_found = 0;
	          regex = {regex, "\\", "\\"};
	       end
           else if (one_char == "(")begin
	          regex_not_found = 0;
	          regex = {regex, "\("};
	       end
           else if (one_char == ")")begin
	          regex_not_found = 0;
	          regex = {regex, "\)"};
	       end
           else if (one_char == "[")begin
	          regex_not_found = 0;
	          regex = {regex, "\\["};
	       end
           else if (one_char == "]")begin
	          regex_not_found = 0;
	          regex = {regex, "\\]"};
	       end
           else begin
	          regex = {regex, one_char};
	       end
        end 
	if(regex_not_found || first_char_regex)  regex = {"^",regex,"$"};
	else regex = {regex,"$"};
     end 
     //
     // The input string is a POSIX regular expression
     //
     else if (pattern.len() > 2 && pattern[0] == "/" && pattern[pattern.len()-1] == "/") begin
        regex = pattern.substr(1, pattern.len()-2);
     end
     // The input string must be literal
     else begin
	for (int i=0; i<pattern.len(); i++) begin
	   string one_char ;
	   one_char = `_TO_CAST_TO_STRING(pattern.getc(i));
	   if (one_char == "." ||
	      one_char == "*" ||
	      one_char == "?" ||
	      one_char == "+" ||
	      one_char == "^" ||
	      one_char == "$" ||
	      one_char == "\\" ||
	      one_char == "(" ||
	      one_char == ")" ||
	      one_char == "[" ||
	      one_char == "]")   regex = {regex, "\\",one_char};
	   else regex = {regex, one_char};
	end
       regex = {regex,"$"};
     end
    return regex;
  endfunction:compile_pattern

  function bit vmm_path_match::match(`vmm_path_compiled name, `vmm_path_regexp pattern);
    bit status;
    status = `vmm_str_match(name,pattern);
    return status;
  endfunction:match
