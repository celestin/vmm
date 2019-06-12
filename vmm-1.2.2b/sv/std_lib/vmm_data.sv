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


// //////////////////////////////////////////// 
// Class: vmm_data
//
// A base class for modeling transactions.
//  
// Function: new 
// 
// Creates a new instance of this data model or transaction descriptor, with the specified
// message service interface. The specified message service interface is used when constructing
// the notify property. 
// 
//|   
//|   Because of the potentially large number of instances of data objects, a class-static message service interface should be used to minimize memory usage and to control class-generic messages:
//|   class eth_frame extends vmm_data {
//|      static vmm_log log = new(eth_frame, class);
//|      function new();
//|         super.new(this.log);
//|         ...
//|      endfunction
//|   endclass: eth_frame
function vmm_data::new(vmm_log log = null
                       `VMM_DATA_BASE_NEW_EXTERN_ARGS);
`ifdef VMM_DATA_BASE_NEW_CALL
   super.new(`VMM_DATA_BASE_NEW_CALL);
`endif

   if (log == null) log = this.get_vmm_log();
`ifndef VMM_DATA_NO_NOTIFY_ALL
   this.notify = new(log);
`ifdef VMM_12_UNDERPIN_VMM_DATA
`ifdef VMM_12_UNDERPIN_VMM_NOTIFY
   if (parent != null) begin
   `VMM_OBJECT_SET_PARENT(this.notify, this)
   end
`endif
`endif

   void'(this.notify.configure(EXECUTE, vmm_notify::ON_OFF));
   void'(this.notify.configure(STARTED, vmm_notify::ON_OFF));
   void'(this.notify.configure(ENDED,   vmm_notify::ON_OFF));
   this.notify.indicate(EXECUTE);
`endif //VMM_DATA_NO_NOTIFY_ALL
endfunction: new


function vmm_log vmm_data::set_log(vmm_log log);
`ifndef VMM_DATA_NO_NOTIFY_ALL
   set_log = this.notify.log;
   this.notify.log = log;
`endif // VMM_DATA_NO_NOTIFY_ALL
endfunction: set_log


function string vmm_data::this_class_name();
   return "vmm_data";
endfunction: this_class_name


function vmm_log vmm_data::get_vmm_log();
`ifndef VMM_DATA_NO_NOTIFY_ALL
   if (this.notify == null) return null;
   return this.notify.log;
`endif // VMM_DATA_NO_NOTIFY_ALL
endfunction


// //////////////////////////////////////////// 
// Function: display 
// 
// Displays the current value of the transaction or data described by this instance, in
// a human-readable format on the standard output. Each line of the output will be prefixed
// with the specified prefix. This method prints the value returned by the psdisplay()
// method. 
// 
function void vmm_data::display(string prefix="");
   $display(this.psdisplay(prefix));
endfunction: display


// //////////////////////////////////////////// 
// Function: psdisplay 
// 
// Returns an image of the current value of the transaction or data described by this instance,
// in a human-readable format as a string. The string may contain newline characters to
// split the image across multiple lines. Each line of the output must be prefixed with
// the specified prefix. 
// 
function string vmm_data::psdisplay(string prefix="");
   $sformat(psdisplay, "%0sclass %s (%0d.%0d.%0d)", prefix,
            this.this_class_name(), this.stream_id, this.scenario_id, this.data_id);
endfunction: psdisplay


// //////////////////////////////////////////// 
// Function: is_valid 
// 
// Checks whether the current value of the transaction or data described by this instance
// is valid and error free, according to the optionally specified kind or format. Returns
// TRUE (non-zero), if the content of the object is valid. Otherwise, it returns FALSE.
// The meaning (and use) of the kind argument is descriptor-specific, and defined by the
// user extension of this method. 
// If silent is TRUE (non-zero), and if the content is invalid, then no error or warning
// messages are generated. If silent is FALSE, and if the content is invalid, then warning
// or error messages may be generated. 
// 
function bit vmm_data::is_valid(bit silent = 1,
                                int kind = -1);
  is_valid = 1;
endfunction: is_valid


// //////////////////////////////////////////// 
// Function: allocate 
// 
// Allocates a new instance of the same type as the object instance. Returns a reference
// to the new instance. Useful to implement class factories to create instances of user-defined
// derived class in generic code written using the base class type. 
// 
function vmm_data vmm_data::allocate();
   string msg = "Virtual vmm_data::allocate() not implemented in derivative";
   vmm_log log = this.get_vmm_log();
   if (log == null) begin
     $display(msg);
     $finish;
   end
   else `vmm_fatal(log, msg);
   allocate = null;
endfunction: allocate


// //////////////////////////////////////////// 
// Function: copy 
// 
// Copies the current value of the object instance to the specified object instance. If
// no target object instance is specified, a new instance is allocated. Returns a reference
// to the target instance. 
// 
//|   
//|   The following trivial implementation does not work. Constructor copying is a shallow copy. The objects instantiated in the object (such as those referenced by the log and notify properties) are not copied, and both copies will share references to the same service interfaces. Moreover, it does not properly handle the case when the to argument is not null.
//|   Invalid implementation of the copy method:
//|   function vmm_data atm_cell::copy(vmm_data to = null) copy = new(this);
//|   endfunction
//|   
//|   The following implementation is usually preferable:
//|   Proper implementation of the copy method:
//|   function vmm_data atm_cell::copy(vmm_data to = null)
//|      atm_cell cpy;
//|   
//|      if (to != null) begin
//|         if ($cast(cpy, to)) begin
//|            vmm_fatal(log, "Not an atm_cell instance");
//|            return null;
//|         end
//|      end else cpy = new;
//|      
//|      this.copy_data(cpy);
//|      cpy.vpi = this.vpi;
//|      ...
//|      copy = cpy;
//|   endfunction: copy
//|   
//|   The base-class implementation of this method must not be called, as it contains error detection code of a derived class that forgot to supply an implementation. The copy_data method should be called, instead.
function vmm_data vmm_data::copy(vmm_data to = null);
   string msg = "Virtual vmm_data::copy() not implemented in derivative";

   if (to == null) begin
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
   end

   this.copy_data(to);
   return to;
endfunction: copy


// //////////////////////////////////////////// 
// Function: copy_data 
// 
// Copies the current value of all base class data properties in the current data object,
// into the specified data object instance. This method should be called by the implementation
// of the <copy> method, in classes immediately derived from this base class.
// 
// 
function void vmm_data::copy_data(vmm_data to);
   if (to == null) begin
      string msg = "vmm_data::copy_data() called with null reference";
      vmm_log log = this.get_vmm_log();

      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return;
   end
   else begin
`ifdef VMM_DATA_BASE_COPY_DATA_CALL
      `VMM_DATA_BASE_COPY_DATA_CALL ;
`endif
      to.stream_id   = this.stream_id;
      to.scenario_id = this.scenario_id;
      to.data_id     = this.data_id;
   end
endfunction: copy_data

   


// //////////////////////////////////////////// 
// Function: compare 
// 
// Compares the current value of the object instance with the current value of the specified
// object instance, according to the specified kind. Returns TRUE (non-zero) if the value
// is identical. Returns FALSE, if the value is different, and a descriptive text of the
// first difference found is returned in the specified string variable. The kind argument
// may be used to implement different comparison functions (for example, full compare,
// comparison of rand properties only, comparison of all properties physically implemented
// in a protocol, and so on.) 
// 
//|   
//|   function bit check(eth_frame actual)
//|      sb_where_to_find_frame where;
//|      eth_frame              q[$];
//|      eth_frame              expect;
//|   
//|      check = 0;
//|      if (!index_tbl[hash(actual)].exists()) return;
//|      where = index_tbl[hash(actual)];
//|      q = sb.port[where.port_no].queue[where.queue_no];
//|      expect = q.pop_front();
//|      if (actual.compare(expect)) check = 1;
//|   endfunction: check
function bit vmm_data::compare(       vmm_data to,
                               output string   diff,
                               input  int      kind = -1);
   return 1;
endfunction : compare


function int unsigned vmm_data::__vmm_byte_size(int kind = -1);
   return 0;
endfunction : __vmm_byte_size


// //////////////////////////////////////////// 
// Function: byte_size 
// 
// Returns the number of bytes required to pack the content of this descriptor. This method
// will be more efficient than the <byte_pack> method, for knowing how many
// bytes are required by the descriptor, because no packing is actually done. 
// If the data can be interpreted or packed in different ways, the kind argument can be used
// to specify which interpretation or packing to use. 
// 
function int unsigned vmm_data::byte_size(int kind = -1);
   return 0;
endfunction : byte_size


// //////////////////////////////////////////// 
// Function: max_byte_size 
// 
// Returns the maximum number of bytes, which are required to pack the content of any instance
// of this descriptor. A value of 0 indicates an unknown maximum size. Thsi method can be
// used to allocate memory buffers in the DUT or verification environment of suitable
// sizes. 
// If the data can be interpreted or packed in different ways, the kind argument can be used
// to specify which interpretation or packing to use. 
// 
function int unsigned vmm_data::max_byte_size(int kind = -1);
   max_byte_size = 0;
endfunction : max_byte_size


// //////////////////////////////////////////// 
// Function: byte_pack 
// 
// Packs the content of the transaction or data into the specified dynamic array of bytes,
// starting at the specified offset in the array. The array is resized appropriately.
// Returns the number of bytes added to the array. 
// If the data can be interpreted or packed in different ways, the kind argument can be used
// to specify which interpretation or packing to use. 
// 
function int unsigned vmm_data::byte_pack(ref   logic [7:0]  bytes[],
                                          input int unsigned offset = 0,
                                          input int          kind = -1);
   return 0;
endfunction : byte_pack




// //////////////////////////////////////////// 
// Function: byte_unpack 
// 
// Unpacks the specified number of bytes of data from the specified offset, in the specified
// dynamic array into this descriptor. If the number of bytes to unpack is specified as
// -1, the maximum number of bytes will be unpacked. Returns the number of bytes unpacked.
// If there is not enough data in the dynamic array to completely fill the descriptor, the
// remaining properties are set to unknown and a warning is generated. 
// If the data can be interpreted or unpacked in different ways, the kind argument can be
// used to specify which interpretation or packing to use. 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      typedef enum {UNTAGGED, TAGGED, CONTROL}
//|         frame_formats_e;
//|      rand frame_formats_e format;
//|      ...
//|      rand bit [47:0] dst;
//|      rand bit [47:0] src;
//|      rand bit        cfi;
//|      rand bit [ 2:0] user_priority;
//|      rand bit [11:0] vlan_id;
//|      ...
//|      virtual function int unsigned byte_unpack(
//|         const ref logic [7:0] array[],
//|         input int unsigned    offset = 0,
//|         input int             len    = -1,
//|         input int             kind   = -1);
//|         integer i;
//|      
//|         i = offset;
//|         this.format = UNTAGGED;
//|         ...
//|         if ({array[i], array[i+1]} === 16h8100) begin
//|            this.format = TAGGED;
//|            i += 2;
//|            ...
//|            {this.user_priority, this.cfi, this.vlan_id} =
//|               {array[i], array[i+2]};
//|            i += 2;
//|            ...
//|         end
//|         ...
//|      endfunction: byte_unpack
//|      ...
//|   endclass: eth_frame
function int unsigned vmm_data::byte_unpack(const ref logic [7:0] bytes[],
                                            input int unsigned    offset = 0,
                                            input int             len = -1,
                                            input int             kind = -1);
   return 0;
endfunction : byte_unpack


// //////////////////////////////////////////// 
// Function: do_psdisplay 
// 
// This method overrides the default implementation of the <psdisplay> method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_psdisplay()). 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      virtual function string do_psdisplay(string prefix = "")
//|         $sformat(psdisplay, "%sEthernet Frame #%0d.%0d.%0d:\n",
//|                prefix, this.stream_id, this.scenario_id,
//|                this.data_id);
//|         ...
//|      endfunction
//|   endclass
function string vmm_data::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction: do_psdisplay


// //////////////////////////////////////////// 
// Function: do_is_valid 
// 
// This method overrides the default implementation of the <is_valid() method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. The default implementation of this method in the vmm_data
// base class must not be called (for example, do not call super.do_is_valid>). 
// If specified argument silent equals 1, no error or warning messages are issued if the
// content is invalid. If silent is FALSE, warning or error messages may be issued if the
// content is invalid. The meaning and use of the argument kind argument is descriptor-specific
// and defined by the user extension of this method. 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      virtual bit function do_is_valid(bit silent = 1,
//|            int kind = -1);
//|         do_is_valid = 1;
//|         if (!do_is_valid && !silent) begin
//|   	 `vmm_error(this.log, "Ethernet Frame is not valid");
//|         end
//|      endfunction
//|   endclass
function bit vmm_data::do_is_valid(bit silent = 1,
                                   int kind = -1);
  this.__vmm_done_user = 0;
  return 0;
endfunction: do_is_valid


function vmm_data vmm_data::do_allocate();
   this.__vmm_done_user = 0;
   return null;
endfunction: do_allocate


// //////////////////////////////////////////// 
// Function: do_copy 
// 
// This method overrides the default implementation of the <copy> method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_copy()). 
// The optional to argument specifies the transaction on which copy needs to be performed.
// 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      virtual vmm_data function do_copy(vmm_data to = null);
//|         eth_frame cpy;
//|         if (to != null) begin
//|            if (!$cast(cpy, to)) begin
//|   	    `vmm_error(this.log, "Cannot copy to non-eth_frame\n
//|               instance");
//|   	    return null;
//|   	 end
//|         end else cpy = new;
//|         ...
//|         `ifdef ETH_USE_COMPOSITION
//|   	 if (this.vlan != null) begin
//|         	    cpy.vlan = new;
//|         	    cpy.vlan.user_priority = this.vlan.user_priority;
//|         	    cpy.vlan.cfi           = this.vlan.cfi;
//|         	    cpy.vlan.id            = this.vlan.id;
//|         	 end
//|         `else
//|            cpy.user_priority = this.user_priority;
//|            cpy.cfi           = this.cfi;
//|            cpy.vlan_id       = this.vlan_id;
//|         `endif
//|         ...
//|         do_copy = cpy;
//|      endfunction
//|      ...
//|   endclass
function vmm_data vmm_data::do_copy(vmm_data to = null);
   this.__vmm_done_user = 0;
   return null;
endfunction: do_copy

   
// //////////////////////////////////////////// 
// Function: do_compare 
// 
// This method overrides the default implementation of the <compare> method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_compare()). 
// The specified argument to is transaction instance with which current transaction
// is compared, returns TRUE if the value is identical. If the value is different, FALSE
// is returned and a descriptive text of the first difference found is returned in the specified
// string variable diff. 
// The kind argument may be used to implement different comparison functions (for example,
// full compare, comparison of rand properties only, comparison of all properties physically
// implemented in a protocol and so on.) 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      virtual bit function do_compare(input vmm_data to =
//|            null,output string diff, input int kind = -1);
//|         eth_frame fr;
//|         do_compare = 1;
//|         ...
//|         `ifdef ETH_USE_COMPOSITION
//|   	 if (fr.vlan == null) begin
//|         	    diff = "No vlan data";
//|   	    do_compare = 0;
//|         	 end
//|   
//|         	 if (fr.vlan.user_priority !==
//|               this.vlan.user_priority) begin
//|         	    $sformat(diff, "user_priority (3'd%0d !== 3'd%0d)",
//|         	             this.vlan.user_priority,
//|                      fr.vlan.user_priority);
//|   	    do_compare = 0;
//|         	 end
//|   	 ...
//|         `else
//|   	 if (fr.user_priority !== this.user_priority) begin
//|         	    $sformat(diff, "user_priority (3'd%0d !== 3'd%0d)",
//|         	             this.user_priority, fr.user_priority);
//|   	    do_compare = 0;
//|         	 end
//|   	 ...
//|         `endif
//|         ...
//|      endfunction
//|   endclass
function bit vmm_data::do_compare(       vmm_data to,
                                  output string   diff,
                                  input  int      kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_compare


// //////////////////////////////////////////// 
// Function: do_byte_size 
// 
// This method overrides the default implementation of the <byte_size> method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_byte_size()). 
// The returned value is the number of bytes required to pack the content of this descriptor.
// The specified kind argument can be used to specify which interpretation or packing
// to use. 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      virtual int function do_byte_size(int kind = -1);
//|         `ifdef TAGGED
//|   	 do_byte_size = 14 + data.size();
//|         `else
//|   	 do_byte_size = 14 + data.size() + 4;
//|         `endif
//|      endfunction
//|   endclass
function int unsigned vmm_data::do_byte_size(int kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_size


// //////////////////////////////////////////// 
// Function: do_max_byte_size 
// 
// This method overrides the default implementation of the <max_byte_size>
// method that is created by the vmm_data shorthand macros. If defined, this method is
// used instead of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_max_byte_size()). 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      virtual int function do_max_byte_size(int kind = -1);
//|         `ifdef JUMBO_PACKET
//|   	 do_max_byte_size = 9000;
//|         `else
//|   	 do_max_byte_size = 1500;
//|         `endif
//|      endfunction
//|   endclass
function int unsigned vmm_data::do_max_byte_size(int kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_max_byte_size


// //////////////////////////////////////////// 
// Function: do_byte_pack 
// 
// This method overrides the default implementation of the <byte_pack> method
// that is created by the vmm_data shorthand macros. If defined, this method is used instead
// of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_byte_pack()). 
// The specified argument bytes is the dynamic array in which transaction contents are
// packed, starting at the specified offset value. The specified argument kind can be
// used to specify which interpretation or packing to use. 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      virtual int function do_byte_pack(ref logic [7:0]
//|           bytes[],input int unsigned offset = 0, 
//|           input int kind = -1);
//|         int i;
//|         ...
//|         `ifdef ETH_USE_COMPOSITION
//|            {bytes[i], bytes[i+1]} = {this.vlan.user_priority,
//|                this.vlan.cfi, this.vlan.id};
//|         `else
//|            {bytes[i], bytes[i+1]} = {this.user_priority,
//|                this.cfi, this.vlan_id};
//|         `endif
//|         ...
//|      endfunction
//|   
//|   endclass
function int unsigned vmm_data::do_byte_pack(ref   logic [7:0]  bytes[],
                                             input int unsigned offset = 0,
                                             input int          kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_pack


// //////////////////////////////////////////// 
// Function: do_byte_unpack 
// 
// This method overrides the default implementation of the <byte_unpack>
// method that is created by the vmm_data shorthand macros. If defined, this method is
// used instead of the default implementation. 
// The default implementation of this method in the vmm_data base class must not be called
// (for example, do not call super.do_byte_unpack()). 
// The specified argument len is the number of data bytes to unpack, starting at specified
// offset value. The unpacked data is stored in the specified bytes dynamic array. 
// If the number of bytes to unpack is specified as -1, the maximum number of bytes will be
// unpacked. This method returns the number of bytes unpacked. 
// If the data can be interpreted or unpacked in different ways, the kind argument can be
// used to specify which interpretation or packing to used. 
// 
//|   
//|   class eth_frame extends vmm_data;
//|      ...
//|      virtual int function do_byte_unpack(const ref logic [7:0]
//|          bytes[],input int unsigned offset = 0,
//|          input int len = -1,input int kind = -1);
//|         ...
//|         `ifdef ETH_USE_COMPOSITION
//|   	 {this.vlan.user_priority, this.vlan.cfi,
//|             this.vlan.id} = {bytes[i], bytes[i+1]};
//|         `else
//|   	 {this.user_priority, this.cfi, this.vlan_id} =
//|            {bytes[i], bytes[i+1]};
//|         `endif
//|         ...
//|      endfunction
//|      ...
//|   endclass
function int unsigned vmm_data::do_byte_unpack(const ref logic [7:0] bytes[],
                                               input int unsigned    offset =0,
                                               input int             len = -1,
                                               input int             kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_unpack



// //////////////////////////////////////////// 
// Function: load 
// 
// Sets the content of this descriptor from the data, in the specified file. The format
// is user defined, and may be binary. By default, interprets a complete line as binary
// byte data and unpacks it. 
// Should return FALSE (zero), if the loading operation was not successful. 
// 
function bit vmm_data::load(int file);
   int len, i;
   logic [7:0] bytes[];
   bit escaped = 0;

   load = 0;

   // Expect one record for the object, with the following format:
   // [<blanks>]<n><SPACE><n bytes (potentially inclusing \n)>\n
   if ($fscanf(file, " %d", len) != 1) begin
      string msg = "Invalid input record in vmm_data::load()";
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return 0;
   end

   // Skip the <SPACE>
   begin
      bit [7:0] c;
      c = $fgetc(file);
   end

   // Read the next 'len' characters and unpack
   bytes = new [len];
   i = 0;
   while (i < len) begin
      int c = $fgetc(file);
      if (c < 0) begin
         string msg = "Truncated input record in vmm_data::load()";
         vmm_log log = this.get_vmm_log();
         if (log == null) begin
            $display(msg);
            $finish;
         end
         else`vmm_fatal(log, msg);
         return 0;
      end
      bytes[i] = c;
      // Some characters have been escaped
      if (bytes[i] == 8'h2E) begin
         escaped = 1;
         continue;
      end
      if (escaped) begin
         bit [7:0] c = bytes[i];
         c[7] = ~c[7];
         bytes[i] = c;
         escaped = 0;
      end
      i++;
   end
   i = this.byte_unpack(bytes);
   if (i != len) begin
      string msg = `vmm_sformatf("Unable to fully unpack input record in vmm_data::load(): %0d bytes were unpacked instead of the full %0d.", len, i);
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return 0;
   end

   // Skip the final \n
   begin
      bit [7:0] c;
      c = $fgetc(file);
      if (c != "\n") begin
         string msg = "Corrupted record in file: extra characters present";
         vmm_log log = this.get_vmm_log();
         if (log == null) begin
            $display(msg);
            $finish;
         end
         else`vmm_fatal(log, msg);
      end
   end

   load = 1;
endfunction: load
   

// //////////////////////////////////////////// 
// Function: save 
// 
// Appends the content of this descriptor to the specified file. The format is user defined,
// and may be binary. By default, packs the descriptor and saves the value of the bytes,
// in sequence, as binary values and terminated by a newline. 
// 
function void vmm_data::save(int file);
   logic [7:0] bytes[];
   int   i;

   // Produce the format expected by vmm_data::load()
   void'(this.byte_pack(bytes));
   $fwrite(file, "%0d ", bytes.size());
   for (i = 0; i < bytes.size(); i++) begin
      bit [7:0] a_byte = bytes[i]; // Make sure there are no X's
      // Some characters need to be escaped
      case (a_byte)
      8'h00,
      8'hFF,
      8'h2E: begin
         bit [7:0] c = a_byte;
         c[7] = ~c[7];
         $fwrite(file, ".%c", c);
      end

      default: $fwrite(file, "%c", a_byte);
      endcase
   end
   $fwrite(file, "\n");
endfunction: save



`ifdef VCS
function int vmm_data::vmt_hook(vmm_xactor xactor = null,
     			        vmm_data   obj = null);
endfunction: vmt_hook

`endif
