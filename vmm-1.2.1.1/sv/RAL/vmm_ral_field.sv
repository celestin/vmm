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


typedef class vmm_ral_field;
class vmm_ral_field_callbacks extends vmm_ral_callbacks;
string fname = "";
int lineno = 0;


   virtual task pre_write(vmm_ral_field                     field,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write

   virtual task post_write(vmm_ral_field                 field,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write

   virtual task pre_read(vmm_ral_field         field,
                         ref vmm_ral::path_e   path,
                         ref string            domain);
   endtask: pre_read

   virtual task post_read(vmm_ral_field                     field,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          vmm_ral::path_e                   path,
                          string                            domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_field_callbacks


class vmm_ral_field 
`ifdef VMM_RAL_BASE
   extends `VMM_RAL_BASE
`endif			
;
   static vmm_log log = new("RAL", "field");

   local string name;
   local vmm_ral::access_e access;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   local vmm_ral_reg parent;
`endif
   local int unsigned lsb;
   local int unsigned size;
   local bit [`VMM_RAL_DATA_WIDTH-1:0] mirrored; // What we think is in the HW
   local bit [`VMM_RAL_DATA_WIDTH-1:0] desired;  // Mirrored after set()
   rand  bit [`VMM_RAL_DATA_WIDTH-1:0] value;    // Mirrored after randomize()
   local bit [`VMM_RAL_DATA_WIDTH-1:0] reset_value;
   local logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset_value;
   local bit written;
   local string fname = "";
   local int lineno = 0;
   local bit read_in_progress;
   local bit write_in_progress;
   local vmm_ral_access        ral_access;
   local int cover_on;
   local bit individually_accessible = 0;

   vmm_ral_field_callbacks XcbsX[$];

   constraint vmm_ral_field_valid {
      if (`VMM_RAL_DATA_WIDTH > size) {
         value < (`VMM_RAL_DATA_WIDTH'h1 << size);
      }
   }

   extern function new(vmm_ral_reg                   parent,
                       string                        name,
                       int unsigned                  size,
                       vmm_ral::access_e             access,
                       bit [`VMM_RAL_DATA_WIDTH-1:0] reset,
                       logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset,
                       int unsigned                  lsb_pos,
                       bit                           is_rand = 0,
                       bit                           cover_on = vmm_ral::NO_COVERAGE,
                       bit                           individually_accessible = 0); 
                                                             // Ignoring cover_on - It is not yet used/supported 
                                                             // in the field level.

   extern virtual function string get_name();
   extern virtual function string get_fullname();
   extern virtual function vmm_ral_reg get_register();
   extern virtual function int unsigned get_lsb_pos_in_register();
   extern virtual function int unsigned get_n_bits();
   extern virtual function vmm_ral::access_e get_access(string domain = "");
   extern virtual function vmm_ral::access_e set_access(vmm_ral::access_e mode);

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");


   /*local*/ extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] XpredictX(bit [`VMM_RAL_DATA_WIDTH-1:0] cur_val,
                                                                             bit [`VMM_RAL_DATA_WIDTH-1:0] wr_val,
                                                                             string                        domain);

   /*local*/ extern virtual function void XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                                  vmm_ral::path_e               path,
                                                  string                        domain);
   /*local*/ extern virtual function void XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                                  vmm_ral::path_e               path,
                                                  string                        domain);
   /*local*/ extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] XupdX();
  
   /*local*/ extern function void Xregister_ral_accessX(vmm_ral_access access);

   extern virtual function void set(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                    string                       fname = "",
                                    int                          lineno = 0);
   extern virtual function bit predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                       string                        fname = "",
                                       int                           lineno = 0,
                                       bit                           force_predict = 0);
   extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] get(string  fname = "",
                                                            int     lineno = 0);
   extern virtual function void reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    set_reset(logic [`VMM_RAL_DATA_WIDTH-1:0] value,
                              vmm_ral::reset_e                kind = vmm_ral::HARD);
   extern virtual function bit needs_update();

   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id =- 1,
                             input  int                           stream_id = -1,
                             input  string                        fname = "",
                             input  int                           lineno = 0);
   extern virtual task read(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                            input  string                       domain = "",
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);
               
   extern virtual task poke(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id =- 1,
                            input  int                           stream_id = -1,
                            input  string                        fname = "",
                            input  int                           lineno = 0);
   extern virtual task peek(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);
               
   extern virtual task mirror(output vmm_rw::status_e status,
                              input  vmm_ral::check_e check = vmm_ral::QUIET,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                              input  string           domain = "",
                              input  string           fname = "",
                              input  int              lineno = 0);

   extern function void prepend_callback(vmm_ral_field_callbacks cb,
                                         string                  fname = "",
                                         int                     lineno = 0);
   extern function void append_callback(vmm_ral_field_callbacks cb,
                                        string                  fname = "",
                                        int                     lineno = 0);
   extern function void unregister_callback(vmm_ral_field_callbacks cb);

   extern function void pre_randomize();
   extern function void post_randomize();
endclass: vmm_ral_field


function vmm_ral_field::new(vmm_ral_reg                   parent,
                            string                        name,
                            int unsigned                  size,
                            vmm_ral::access_e             access,
                            bit [`VMM_RAL_DATA_WIDTH-1:0] reset,
                            logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset,
                            int unsigned                  lsb_pos,
                            bit                           is_rand = 0,
                            bit                           cover_on = vmm_ral::NO_COVERAGE,
                            bit                           individually_accessible = 0); 
                                                             // Ignoring cover_on - It is not yet used/supported 
                                                             // in the field level.
 `ifdef VMM_12_UNDERPIN_VMM_RAL  
   super.new(parent, name);
   this.set_object_name(name, "RAL");
 `else 
   this.parent = parent;
 `endif		
   this.name   = name;

   if (size == 0) begin
      `vmm_error(this.log, $psprintf("Field \"%s\" cannot have 0 bits", name));
      size = 1;
   end
   if (size > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Field \"%s\" cannot have more than %0d bits",
                                     name, `VMM_RAL_DATA_WIDTH));
      size = `VMM_RAL_DATA_WIDTH;
   end
   this.size   = size;

   this.access = access;
   this.reset_value = reset;
   this.soft_reset_value = soft_reset;
   this.lsb    = lsb_pos;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.register_field(this);
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      parent.register_field(this); 
   end
`endif
   this.individually_accessible = individually_accessible;
   this.cover_on = cover_on;
   if (!is_rand) this.value.rand_mode(0);

   this.written = 0;

endfunction: new


function string vmm_ral_field::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_field::get_fullname();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_fullname = {this.parent.get_fullname(), ".", this.name};
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      get_fullname = {parent.get_fullname(), ".", this.name};
   end
`endif
endfunction: get_fullname


function vmm_ral_reg vmm_ral_field::get_register();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_register = this.parent;
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      get_register = parent;
   end
`endif
endfunction: get_register


function int unsigned vmm_ral_field::get_lsb_pos_in_register();
   get_lsb_pos_in_register = this.lsb;
endfunction: get_lsb_pos_in_register


function int unsigned vmm_ral_field::get_n_bits();
   get_n_bits = this.size;
endfunction: get_n_bits


function vmm_ral::access_e vmm_ral_field::get_access(string domain = "");
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_reg parent;
   $cast(parent, this._parent);
`endif

   get_access = this.access;
   if (parent.get_n_domains() == 1 || domain == "BaCkDoOr") return get_access;

   // Is the register restricted in this domain?
   case (parent.get_rights(domain))
     vmm_ral::RW:
       // No restrictions
       return get_access;

     vmm_ral::RO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::RO,
         vmm_ral::W1,
         vmm_ral::W1C: get_access = vmm_ral::RO;

         vmm_ral::RU,
         vmm_ral::A0,
         vmm_ral::A1: get_access = vmm_ral::RU;

         vmm_ral::WO: begin
            `vmm_error(this.log,
                       $psprintf("WO field \"%s\" restricted to RO in domain \"%s\"",
                                 this.get_name(), domain));
         end

         // No change for the other modes (OTHER, USERx)
       endcase

     vmm_ral::WO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::WO: get_access = vmm_ral::WO;

         vmm_ral::RO,
         vmm_ral::RU,
         vmm_ral::W1C,
         vmm_ral::A0,
         vmm_ral::A1: begin
            `vmm_error(this.log,
                       $psprintf("%s field \"%s\" restricted to WO in domain \"%s\"",
                                 get_access.name(), this.get_name(), domain));
         end

         // No change for the other modes (W1, OTHER, USERx)
       endcase

     default:
       `vmm_error(this.log,
                  $psprintf("Shared register \"%s\" containing field \"%s\" is not shared in domain \"%s\"",
                            parent.get_name(), this.get_name(), domain));
   endcase
endfunction: get_access


function vmm_ral::access_e vmm_ral_field::set_access(vmm_ral::access_e mode);
   set_access = this.access;
   this.access = mode;
endfunction: set_access


function void vmm_ral_field::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display


function string vmm_ral_field::psdisplay(string prefix = "");
   string fmt;
   string res_str = "";
   string t_str = "";
   bit with_debug_info = 0;

   $sformat(fmt, "%0d'h%%%0dh", this.get_n_bits(),
            (this.get_n_bits()-1)/4 + 1);
   $sformat(psdisplay, {"%s%s[%0d-%0d] = ",fmt,"%s"}, prefix,
            this.get_name(),
            this.get_lsb_pos_in_register() + this.get_n_bits() - 1,
            this.get_lsb_pos_in_register(), this.desired,
            (this.desired != this.mirrored) ? $psprintf({" (Mirror: ",fmt,")"}, this.mirrored) : "");

   if (read_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay = {psdisplay, "\n", res_str, "currently executing read method"}; 
   end
   if ( write_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay = {psdisplay, "\n", res_str, "currently executing write method"}; 
   end

   foreach ( this.XcbsX[i]) begin
      if (this.XcbsX[i].fname != "" && this.XcbsX[i].lineno != 0) begin
         string tmp_str = "";
         with_debug_info = 1'b1;
         $sformat(tmp_str, "callback registered in %s:%0d\n",this.XcbsX[i].fname, this.XcbsX[i].lineno);
         res_str = {res_str, tmp_str};
      end
   end
   if (XcbsX.size() != 0) begin
      $sformat(t_str, "\nTotal %0d callbacks have been registered for %s",XcbsX.size(), this.get_name());
      psdisplay= {psdisplay, t_str};
   end
   if (with_debug_info == 1'b1) begin
      psdisplay= {psdisplay, "\ncallbacks with debug info.."};
      psdisplay= {psdisplay, "\n", res_str };
   end
endfunction: psdisplay



function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::XpredictX(bit [`VMM_RAL_DATA_WIDTH-1:0] cur_val,
                                                                bit [`VMM_RAL_DATA_WIDTH-1:0] wr_val,
                                                                string                        domain);

   case (this.get_access(domain))
     vmm_ral::RW:    return wr_val;
     vmm_ral::RO:    return cur_val;
     vmm_ral::WO:    return wr_val;
     vmm_ral::W1:    return (this.written) ? cur_val : wr_val;
     vmm_ral::RU:    return cur_val;
     vmm_ral::RC:    return cur_val;
     vmm_ral::W1C:   return cur_val & (~wr_val);
     vmm_ral::A0:    return cur_val | wr_val;
     vmm_ral::A1:    return cur_val & wr_val;
     vmm_ral::DC:    return wr_val;
     vmm_ral::OTHER,
     vmm_ral::USER0,
     vmm_ral::USER1,
     vmm_ral::USER2,
     vmm_ral::USER3: return wr_val;
   endcase

   `vmm_fatal(log, "vmm_ral_field::XpredictX(): Internal error");
   return 0;
endfunction: XpredictX


function void vmm_ral_field::XforceX(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                     vmm_ral::path_e              path,
                                     string                       domain);
   value &= ('b1 << this.size)-1;

   // If the value was obtained via a front-door access
   // then a RC field will have been cleared
   if (path == vmm_ral::BFM && this.get_access(domain) == vmm_ral::RC) begin
      value = 0;
   end

   // If the value of a WO field was obtained via a front-door access
   // it will always read back as 0 and the value of the field
   // cannot be inferred from it
   if (path == vmm_ral::BFM && this.get_access(domain) == vmm_ral::WO) return;

   this.mirrored = value;
   this.desired = value;
   this.value   = value;
endfunction: XforceX


function void vmm_ral_field::XwroteX(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                     vmm_ral::path_e              path,
                                     string                       domain);
   if (value >> this.size) begin
      `vmm_warning(this.log, $psprintf("Specified value (0x%h) greater than field \"%s\" size (%0d bits)",
                                       value, this.get_name(), this.size));
      value &= ('b1 << this.size)-1;
   end

   if (path == vmm_ral::BFM) begin
      this.mirrored = this.XpredictX(this.mirrored, value, domain);
   end
   else this.mirrored = value;

   this.desired = this.mirrored;
   this.value   = this.mirrored;

   this.written = 1;
endfunction: XwroteX


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::XupdX();
   // Figure out which value must be written to get the desired value
   // given what we think is the current value in the hardware
   XupdX = 0;

   case (this.access)
      vmm_ral::RW:    XupdX = this.desired;
      vmm_ral::RO:    XupdX = this.desired;
      vmm_ral::WO:    XupdX = this.desired;
      vmm_ral::W1:    XupdX = this.desired;
      vmm_ral::RU:    XupdX = this.desired;
      vmm_ral::RC:    XupdX = this.desired;
      vmm_ral::W1C:   XupdX = ~this.desired;
      vmm_ral::A0:    XupdX = this.desired;
      vmm_ral::A1:    XupdX = this.desired;
      vmm_ral::DC,
      vmm_ral::OTHER,
      vmm_ral::USER0,
      vmm_ral::USER1,
      vmm_ral::USER2,
      vmm_ral::USER3: XupdX = this.desired;
   endcase
endfunction: XupdX

function void vmm_ral_field::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("Field \"%s\" is already used by another RAL access instance", this.get_name()));
   end
   this.ral_access = access;

endfunction: Xregister_ral_accessX

function void vmm_ral_field::set(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                 string                       fname = "",
                                 int                          lineno = 0);
   this.fname = fname;
   this.lineno = lineno;
   if (value >> this.size) begin
      `vmm_warning(this.log, $psprintf("Specified value (0x%h) greater than field \"%s\" size (%0d bits)",
                                       value, this.get_name(), this.size));
      value &= ('b1 << this.size)-1;
   end

   case (this.access)
      vmm_ral::RW:    this.desired = value;
      vmm_ral::RO:    this.desired = this.desired;
      vmm_ral::WO:    this.desired = value;
      vmm_ral::W1:    this.desired = (this.written) ? this.desired : value;
      vmm_ral::RU:    this.desired = this.desired;
      vmm_ral::RC:    this.desired = this.desired;
      vmm_ral::W1C:   this.desired &= (~value);
      vmm_ral::A0:    this.desired |= value;
      vmm_ral::A1:    this.desired &= value;
      vmm_ral::DC,
      vmm_ral::OTHER,
      vmm_ral::USER0,
      vmm_ral::USER1,
      vmm_ral::USER2,
      vmm_ral::USER3: this.desired = value;
   endcase
   this.value = this.desired;
endfunction: set

 
function bit vmm_ral_field::predict(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                    string                       fname = "",
                                    int                          lineno = 0, 
                                    bit                          force_predict = 0);
   this.fname = fname;
   this.lineno = lineno;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (this.parent.Xis_busyX && !force_predict) begin
      `vmm_warning(this.log, $psprintf("Trying to predict value of field \"%s\" while register \"%s\" is being accessed",
                                       this.get_name(),
                                       this.parent.get_fullname()));
      return 0;
   end
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      if (parent.Xis_busyX && !force_predict) begin
         `vmm_warning(this.log, $psprintf("Trying to predict value of field \"%s\" while register \"%s\" is being accessed",
                                       this.get_name(),
                                       parent.get_fullname()));
         return 0;
      end
   end
`endif
   
   value &= ('b1 << this.size)-1;
   this.mirrored = value;
   this.desired = value;
   this.value   = value;

   return 1;
endfunction: predict


function bit[`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::get(string  fname = "",
                                                         int     lineno = 0);
   this.fname = fname;
   this.lineno = lineno;
   get = this.desired;
endfunction: get


function void vmm_ral_field::reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   case (kind)
     vmm_ral::HARD: begin
        this.mirrored = reset_value;
        this.desired  = reset_value;
        this.written  = 0;
     end
     vmm_ral::SOFT: begin
        if (soft_reset_value !== 'x) begin
           this.mirrored = soft_reset_value;
           this.desired  = soft_reset_value;
        end
     end
   endcase
   this.value = this.desired;
endfunction: reset


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_field::get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);

   if (kind == vmm_ral::SOFT) return this.soft_reset_value;

   return this.reset_value;
endfunction: get_reset


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_field::set_reset(logic [`VMM_RAL_DATA_WIDTH-1:0] value,
                            vmm_ral::reset_e kind = vmm_ral::HARD);
   case (kind)
     vmm_ral::HARD: begin
        set_reset = this.reset_value;
        this.reset_value = value;
     end
     vmm_ral::SOFT: begin
        set_reset = this.soft_reset_value;
        this.soft_reset_value = value;
     end
   endcase
endfunction: set_reset


function bit vmm_ral_field::needs_update();
   needs_update = (this.mirrored != this.desired);
endfunction: needs_update

task vmm_ral_field::write(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1,
                          input  string                        fname = "",
                          input  int                           lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp,msk,temp_data;
   bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '0;
   bit b_en[$];
   vmm_ral_field fields[];
   int fld_pos = 0;
   bit indv_acc = 0;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
   int w = 0, j = 0,bus_width, n_bits,n_access,n_access_extra,n_bytes_acc,temp_be;
			
   vmm_ral_block  blk;
   vmm_ral_reg    this_reg = this.get_register();
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_reg parent;
   $cast(parent, this._parent);
`endif

   blk = parent.get_block();
			
		
   this.fname = fname;
   this.lineno = lineno;
   this.write_in_progress = 1'b1;

   parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("vmm_ral_field::write(): Value greater than field \"%s\" size", this.get_name()));
      value &= value & ((1<<this.size)-1);
   end
   
temp_data = value;
   tmp = 0;
   // What values are written for the other fields???
   parent.get_fields(fields);
   foreach (fields[i]) begin
      if (fields[i] == this) begin
         tmp |= value << this.lsb;
         fld_pos = i;
         continue;
      end

      // It depends on what kind of bits they are made of...
      case (fields[i].get_access(domain))
        // These...
        vmm_ral::RW,
        vmm_ral::RO,
        vmm_ral::WO,
        vmm_ral::W1,
        vmm_ral::RU,
        vmm_ral::DC,
        vmm_ral::OTHER,
        vmm_ral::USER0,
        vmm_ral::USER1,
        vmm_ral::USER2,
        vmm_ral::USER3:
          // Use their mirrored value
          tmp |= fields[i].get() << fields[i].get_lsb_pos_in_register();

        // These...
        vmm_ral::RC,
        vmm_ral::W1C,
        vmm_ral::A0:
          // Use all 0's
          tmp |= 0;

        // These...
        vmm_ral::A1:
          // Use all 1's
          tmp |= ((1<<fields[i].get_n_bits())-1) << fields[i].get_lsb_pos_in_register();

        default:
          `vmm_fatal(log, "Internal error: write() does not handle field access mode");
      endcase
   end

`ifdef VMM_RAL_NO_INDIVIDUAL_FIELD_ACCESS

   parent.XwriteX(status, tmp, path, domain, data_id, scenario_id, stream_id);

`else	
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Field \"%s\" not associated with RAL access object", this.get_name()));
      return;
   end

   bus_width = blk.get_n_bytes();  //// get the width of the physical interface data bus in bytes
			
/* START to check if this field is the sole occupant of the complete bus_data(width) */
   if(fields.size() == 1) begin
      indv_acc = 1;
   end else begin
   if(fld_pos == 0) begin
     if (fields[fld_pos+1].lsb%(bus_width*8) == 0)  indv_acc = 1;
     else if ((fields[fld_pos+1].lsb - fields[fld_pos].size) >= (fields[fld_pos+1].lsb%(bus_width*8))) indv_acc = 1;
     else indv_acc = 0;
   end 
   else if(fld_pos == (fields.size()-1)) begin
     if (fields[fld_pos].lsb%(bus_width*8) == 0)  indv_acc = 1;
     else if ((fields[fld_pos].lsb - (fields[fld_pos-1].lsb+fields[fld_pos-1].size)) >= (fields[fld_pos].lsb%(bus_width*8))) indv_acc = 1;
     else indv_acc = 0;
   end 
   else begin
     if (fields[fld_pos].lsb%(bus_width*8) == 0) begin
        if (fields[fld_pos+1].lsb%(bus_width*8) == 0) indv_acc = 1;
        else if ((fields[fld_pos+1].lsb - (fields[fld_pos].lsb+fields[fld_pos].size)) >= (fields[fld_pos+1].lsb%(bus_width*8))) indv_acc = 1;
        else indv_acc = 0;
     end 
     else begin
        if(((fields[fld_pos+1].lsb - (fields[fld_pos].lsb+fields[fld_pos].size))>= (fields[fld_pos+1].lsb%(bus_width*8)))  &&
           ((fields[fld_pos].lsb - (fields[fld_pos-1].lsb+fields[fld_pos-1].size))>=(fields[fld_pos].lsb%(bus_width*8))) ) indv_acc = 1;
        else indv_acc = 0;				
     end
   end
   end
/* END to check if this field is the sole occupant of the complete bus_data(width) */
			
   if(path == vmm_ral::DEFAULT) path = blk.get_default_access(); /// blk = parent.get_block();
   if(path == vmm_ral::BFM) begin
     if(this.individually_accessible) begin
       if(this.ral_access.Xsupports_byte_enableX(domain) || (indv_acc)) begin
								
         value = temp_data;
         foreach (this.XcbsX[i]) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, this.XcbsX[i])) continue;
            cb.pre_write(this, value, path, domain);
         end
         parent.Xis_busyX = 1;
         n_access_extra = this.lsb%(bus_width*8);		
         n_access = n_access_extra + this.size;
         value = (value) << (n_access_extra);
	/* calculate byte_enables */
	 temp_be = n_access_extra;
         while(temp_be >= 8) begin
	   b_en.push_back(0);
           temp_be = temp_be - 8;
	 end			
	 temp_be = temp_be + this.size;
     	 while(temp_be > 0) begin
	   b_en.push_back(1);
           temp_be = temp_be - 8;
	 end
	/* end calculate byte_enables */
        if(n_access%8 != 0) n_access = n_access + (8 - (n_access%8)); 
          n_bytes_acc = n_access/8;
  	  w = this.ral_access.Xget_physical_addressesX(this_reg.get_offset_in_block(domain) + (this.lsb/(bus_width*8)),
                                                       0,(n_bytes_acc),
                                                       blk,
                                                       domain, -1,
                                                       addr);
          j = 0;
          n_bits = this.size;
          foreach(addr[i]) begin
	    bit [`VMM_RAL_DATA_WIDTH-1:0] data;
            bit tt;
            data = value >> (j*8);
            
            for(int z=0;z<bus_width;z++) begin
			   `ifndef VCS
                   if(b_en.size() !=0) 
				      begin
                         tt = b_en.pop_front();
                         byte_en[z] = tt;
                      end
               `else
                    tt = b_en.pop_front();
                    byte_en[z] = tt;
               `endif   
            end	
											  
            this.ral_access.write(status, addr[i], data,  (n_bits > w*8) ? w*8 : n_bits, domain,
                                  data_id, scenario_id, stream_id, fname, lineno,byte_en);
            if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) return;
              j += w;
              n_bits -= w * 8;
          end
          /*if (this.cover_on) begin
               this.sample(value, 0, di);
               parent.XsampleX(this.offset_in_block[di], di);
          end*/
          parent.Xis_busyX = 0;
	  value = (value >> (n_access_extra)) & ((1<<this.size))-1;
	  this.XwroteX(value, path, domain);

          foreach (this.XcbsX[i]) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, this.XcbsX[i])) continue;
            cb.post_write(this, value, path, domain, status);
          end
          //`vmm_callback(vmm_ral_field_callbacks,post_read(XcbsX,value,path,domain,status));
       end else begin
         if(!this.ral_access.Xsupports_byte_enableX(domain)) begin
          `vmm_warning(this.log, $psprintf("Protocol doesnot support byte enabling ....\nWriting complete register instead."));
         end		
   	 if(!indv_acc) begin
          `vmm_warning(this.log, $psprintf("Field \"%s\" is not individually accessible ...\nWriting complete register instead.", this.get_name()));
   	 end		
         parent.XwriteX(status, tmp, path, domain, data_id, scenario_id, stream_id);
       end	
     end else begin
       `vmm_warning(this.log, $psprintf("Individual field access not available for field \"%s\". Writing complete register instead.", this.get_name()));
       parent.XwriteX(status, tmp, path, domain, data_id, scenario_id, stream_id);
      end	
   end
   // Individual field access not available for BACKDOOR access		
    if(path == vmm_ral::BACKDOOR) begin
     parent.XwriteX(status, tmp, path, domain, data_id, scenario_id, stream_id);
    end
`endif
   parent.XatomicX(0);
   this.write_in_progress = 1'b0;
endtask: write

task vmm_ral_field::read(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                         input  string                       domain = "",
                         input  int                          data_id = -1,
                         input  int                          scenario_id = -1,
                         input  int                          stream_id = -1,
                         input  string                       fname = "",
                         input  int                          lineno = 0);
   bit[`VMM_RAL_DATA_WIDTH-1:0] reg_value;
   bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '0;
   bit b_en[$];
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
   int w = 0, j = 0,bus_width, n_bits,n_access,n_access_extra,n_bytes_acc,temp_be;
   vmm_ral_field fields[];
   int fld_pos = 0;
   int rh_shift = 0;
   bit indv_acc = 0;
   
   vmm_ral_block  blk;
   vmm_ral_reg    this_reg = this.get_register();
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_reg parent;
   $cast(parent, this._parent);
`endif
			
   blk = parent.get_block();
   this.fname = fname;
   this.lineno = lineno;
   this.read_in_progress = 1'b1;

`ifdef VMM_RAL_NO_INDIVIDUAL_FIELD_ACCESS
   parent.read(status, reg_value, path, domain, data_id, scenario_id, stream_id, fname, lineno); 
   value = (reg_value >> this.lsb) & ((1<<this.size))-1;
`else
   bus_width = blk.get_n_bytes();  //// get the width of the physical interface data bus in bytes
  /* START to check if this field is the sole occupant of the complete bus_data(width) */
   parent.get_fields(fields);
   foreach (fields[i]) begin
      if (fields[i] == this) begin
        fld_pos = i;
      end
   end			
   if(fields.size() == 1) begin
      indv_acc = 1;
   end else begin
      if(fld_pos == 0) begin
        if (fields[fld_pos+1].lsb%(bus_width*8) == 0)  indv_acc = 1;
        else if ((fields[fld_pos+1].lsb - fields[fld_pos].size) >= (fields[fld_pos+1].lsb%(bus_width*8))) indv_acc = 1;
        else indv_acc = 0;
       end 
      else if(fld_pos == (fields.size()-1)) begin
       if (fields[fld_pos].lsb%(bus_width*8) == 0)  indv_acc = 1;
       else if ((fields[fld_pos].lsb - (fields[fld_pos-1].lsb+fields[fld_pos-1].size)) >= (fields[fld_pos].lsb%(bus_width*8))) indv_acc = 1;
       else indv_acc = 0;
      end 
      else begin
       if (fields[fld_pos].lsb%(bus_width*8) == 0) begin
        if (fields[fld_pos+1].lsb%(bus_width*8) == 0) indv_acc = 1;
        else if ((fields[fld_pos+1].lsb - (fields[fld_pos].lsb+fields[fld_pos].size)) >= (fields[fld_pos+1].lsb%(bus_width*8))) indv_acc = 1;
        else indv_acc = 0;
       end 
       else begin
        if(((fields[fld_pos+1].lsb - (fields[fld_pos].lsb+fields[fld_pos].size))>= (fields[fld_pos+1].lsb%(bus_width*8)))  &&
           ((fields[fld_pos].lsb - (fields[fld_pos-1].lsb+fields[fld_pos-1].size))>=(fields[fld_pos].lsb%(bus_width*8))) ) indv_acc = 1;
        else indv_acc = 0;				
       end
      end
   end
/* END to check if this field is the sole occupant of the complete bus_data(width) */

   if(path == vmm_ral::DEFAULT) path = blk.get_default_access(); /// blk = parent.get_block();
   if(path == vmm_ral::BFM) begin
      if(this.individually_accessible) begin
         if(this.ral_access.Xsupports_byte_enableX(domain) || (indv_acc)) begin
	    if (blk.Xis_powered_downX) begin
              `vmm_error(this.log, $psprintf("Field %s cannot be accessed when its parent block is powered down", this.get_fullname()));
               return;
            end
            parent.XatomicX(1);
            parent.Xis_busyX = 1;
	    foreach (this.XcbsX[i]) begin
              vmm_ral_field_callbacks cb;
              if (!$cast(cb, this.XcbsX[i])) continue;
              cb.pre_read(this, path, domain);
            end
			
            n_access_extra = this.lsb%(bus_width*8);		
	    n_access = n_access_extra + this.size;
	    /* calculate byte_enables */
	    temp_be = n_access_extra;
            while(temp_be >= 8) begin
              b_en.push_back(0);
              temp_be = temp_be - 8;
	    end			
	    temp_be = temp_be + this.size;
     	    while(temp_be > 0) begin
	      b_en.push_back(1);
              temp_be = temp_be - 8;
	    end
	   /*end calculate byte_enables */
									
           if(n_access%8 != 0) n_access = n_access + (8 - (n_access%8)); 
             n_bytes_acc = n_access/8;
       	     w = this.ral_access.Xget_physical_addressesX(this_reg.get_offset_in_block(domain) + (this.lsb/(bus_width*8)),
                                                          0,n_bytes_acc,
                                                          blk,
                                                          domain, -1, 
                                                          addr);
             n_bits = this.size;
             foreach(addr[i]) begin
	       bit [`VMM_RAL_DATA_WIDTH-1:0] data;	
	       bit tt;

               for(int z=0;z<bus_width;z++) begin
			      `ifndef VCS
                     if(b_en.size() !=0) 
				        begin
                           tt = b_en.pop_front();
                           byte_en[z] = tt;
                        end
                  `else
                     tt = b_en.pop_front();
                     byte_en[z] = tt;
                  `endif   
               end	

               this.ral_access.read(status, addr[i], data,  (n_bits > w*8) ? w*8 : n_bits, domain,data_id, scenario_id, stream_id, fname, lineno,byte_en);
               if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) return;
   		reg_value |= (data & ((1 << (w*8)) - 1)) << (j*8);
                j += w;
                n_bits -= w * 8;
             end
             parent.Xis_busyX = 0;
	    /*if (this.cover_on) begin
              this_reg.sample(value, 1, domain);
              this_reg.parent.XsampleX(this_reg.offset_in_block[domain], domain);
              end*/
             value = (reg_value >> (n_access_extra)) & ((1<<this.size))-1;
             	     this.XforceX(value, path, domain);
             	     foreach (this.XcbsX[i]) begin
               vmm_ral_field_callbacks cb;
               if (!$cast(cb, this.XcbsX[i])) continue;
               cb.post_read(this, value, path, domain, status);
             end
             parent.XatomicX(0);
	     this.fname = "";
	     this.lineno = 0;
									
   						//`vmm_callback(vmm_ral_field_callbacks,post_read(XcbsX,value,path,domain,status));
   	 end else begin
   	   if(!this.ral_access.Xsupports_byte_enableX(domain)) begin
              `vmm_warning(this.log, $psprintf("Protocol doesnot support byte enabling ....\n Reading complete register instead."));
           end		
   	   if((this.size%8)!=0) begin
           `vmm_warning(this.log, $psprintf("Field \"%s\" is not byte aligned. Individual field access will not be available ...\nReading complete register instead.", this.get_name()));
   	   end		
           parent.read(status, reg_value, path, domain, data_id, scenario_id, stream_id, fname, lineno);
           value = (reg_value >> this.lsb) & ((1<<this.size))-1;
   	 end	
      end else begin
         `vmm_warning(this.log, $psprintf("Individual field access not available for field \"%s\". Reading complete register instead.", this.get_name()));
         parent.read(status, reg_value, path, domain, data_id, scenario_id, stream_id, fname, lineno);
         value = (reg_value >> this.lsb) & ((1<<this.size))-1;
   	end
     end
     /// Individual field access not available for BACKDOOR access		
     if(path == vmm_ral::BACKDOOR) begin
       parent.read(status, reg_value, path, domain, data_id, scenario_id, stream_id, fname, lineno);
       value = (reg_value >> this.lsb) & ((1<<this.size))-1;
     end
`endif
   this.read_in_progress = 1'b0;

endtask: read
               
task vmm_ral_field::poke(output vmm_rw::status_e              status,
                         input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  int                           data_id = -1,
                         input  int                           scenario_id = -1,
                         input  int                           stream_id = -1,
                         input  string                        fname = "",
                         input  int                           lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_reg parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;
   parent.XatomicX(1);
   parent.Xis_locked_by_fieldX = 1'b1;

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("vmm_ral_field::poke(): Value greater than field \"%s\" size", this.get_name()));
      value &= value & ((1<<this.size)-1);
   end

   tmp = 0;
   // What is the current values of the other fields???
   parent.peek(status, tmp, data_id, scenario_id, stream_id, fname, lineno);
   if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) begin
      `vmm_error(log, $psprintf("vmm_ral_field::poke(): Peeking register \"%s\" returned status %s", parent.get_fullname(), status.name()));
      parent.XatomicX(0);
      parent.Xis_locked_by_fieldX = 1'b0;
      return;
   end

   // Force the value for this field then poke the resulting value
   tmp &= ~(((1<<this.size)-1) << this.lsb);
   tmp |= value << this.lsb;
   parent.poke(status, tmp, data_id, scenario_id, stream_id, fname, lineno);

   parent.XatomicX(0);
   parent.Xis_locked_by_fieldX = 1'b0;
endtask: poke


task vmm_ral_field::peek(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  int                          data_id = -1,
                         input  int                          scenario_id = -1,
                         input  int                          stream_id = -1,
                         input  string                       fname = "",
                         input  int                          lineno = 0);
   bit[`VMM_RAL_DATA_WIDTH-1:0] reg_value;

   this.fname = fname;
   this.lineno = lineno;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.peek(status, reg_value, data_id, scenario_id, stream_id, fname, lineno);
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      parent.peek(status, reg_value, data_id, scenario_id, stream_id, fname, lineno);
   end
`endif
   value = (reg_value >> lsb) & ((1<<size))-1;
endtask: peek
               

task vmm_ral_field::mirror(output vmm_rw::status_e status,
                           input  vmm_ral::check_e check = vmm_ral::QUIET,
                           input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                           input  string           domain = "",
                           input  string           fname = "",
                           input  int              lineno = 0);
   this.fname = fname;
   this.lineno = lineno;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.mirror(status, check, path, domain, fname, lineno);
`else
   begin
      vmm_ral_reg parent;
      $cast(parent, this._parent);
      parent.mirror(status, check, path, domain, fname, lineno);
   end
`endif
endtask: mirror


function void vmm_ral_field::prepend_callback(vmm_ral_field_callbacks cb,
                                              string                  fname = "",
                                              int                     lineno = 0);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Prepend new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.XcbsX.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_field::append_callback(vmm_ral_field_callbacks cb,
                                             string                  fname = "",
                                             int                     lineno = 0);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Append new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.XcbsX.push_back(cb);
endfunction: append_callback


function void vmm_ral_field::unregister_callback(vmm_ral_field_callbacks cb);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         int j = i;
         // Unregister it
         this.XcbsX.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with field \"%s\"", this.get_name()));
endfunction: unregister_callback


function void vmm_ral_field::pre_randomize();
   // Update the only publicly known property with the current
   // desired value so it can be used as a state variable should
   // the rand_mode of the field be turned off.
   this.value = this.desired;
endfunction: pre_randomize


function void vmm_ral_field::post_randomize();
   this.desired = this.value;
endfunction: post_randomize