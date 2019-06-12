//
// Template for VMM-compliant transaction descriptor
// <TR>         Name of transaction descriptor class
// <BU>         Name of BU descripton class
//

`ifndef TR__SV
`define TR__SV

class TR extends BU;

   `vmm_typename(TR)
   
   NORMAL_START
   static vmm_log log = new("TR", "class");
  
   NORMAL_END
   // ToDo: Modify/add symbolic transaction identifiers to match
   typedef enum {READ, WRITE } kinds_e;
   rand kinds_e kind;
   typedef enum {IS_OK, ERROR} status_e;
   rand status_e status;
   // ToDo: Add constraint blocks to prevent error injection
   // ToDo: Add relevant class properties to define all transactions
   // ToDo: Modify/add symbolic transaction identifiers to match

   constraint TR_valid {
      // ToDo: Define constraint to make descriptor valid
      status == IS_OK;
   }
   MACRO_START
   
   `vmm_data_member_begin(TR)
      `vmm_data_member_enum(kind, DO_ALL)
      `vmm_data_member_enum(status, DO_ALL)
      // ToDo: add properties using macros here
   
   `vmm_data_member_end(TR)
   MACRO_END
NORMAL_START
   extern function new(string name = "", vmm_object parent = null);
   extern virtual function string psdisplay(string prefix = "");
   extern virtual function bit is_valid(bit       silent = 1,
                                        input int kind   = -1);
   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data cpy = null);
   extern virtual function bit compare(vmm_data to,
                                       output string diff,
                                       input  int    kind = -1);
   extern virtual function int unsigned byte_size(int kind = -1);
   extern virtual function int unsigned byte_pack(ref logic [7:0]    bytes[],
                                                  input int unsigned offset = 0,
                                                  input int          kind   = -1);
   extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                    input int unsigned    offset = 0,
                                                    input int             len    = -1, 
                                                    input int             kind   = -1);
NORMAL_END

   `vmm_class_factory(TR)

endclass: TR


NORMAL_START
function TR::new(string name = "", vmm_object parent = null);
   super.new(log);
   this.set_parent_object(parent);
endfunction: new


function string TR::psdisplay(string prefix = "");
   return $psprintf("%s Status=%s Kind=%s", prefix, status.name(), kind.name());
    // ToDo: Implement this method

endfunction: psdisplay


function bit TR::is_valid(bit silent = 1,
                          input int kind = -1);
 // ToDo: Implement this method

endfunction: is_valid


function vmm_data TR::allocate();
   TR tr = new(this.get_object_name(), get_parent());
   allocate = tr;
endfunction: allocate


function vmm_data TR::copy(vmm_data cpy = null);
   TR to;

   // Copying to a new instance?
   if (cpy == null) 
      to = new(this.get_object_name(), get_parent());
    else 
      // Copying to an existing instance. Correct type?
      if (!$cast(to, cpy)) begin 
         `vmm_fatal(this.log, "Attempting to copy to a non TR instance");
         return null;
     end 

   super.copy_data(to);

   to.kind = this.kind;

   // ToDo: Copy additional class properties
   copy = to;  
endfunction: copy


function bit TR::compare(vmm_data   to,
                         output string diff,
                         input int  kind = -1);
   TR tr;
    
   compare = 0;
   if (to == null) begin 
      `vmm_fatal(this.log, "Cannot compare to NULL instance");
      return 0;
   end

   if (!$cast(tr,to)) begin 
      `vmm_fatal(this.log, "Attempting to compare to a non TR instance");
      return 0;
   end

   if (this.kind != tr.kind) begin
      $sformat(diff, "Kind %0s != %0s", this.kind, tr.kind);
      return 0;
   end
   // ToDo: Compare additional class properties

   compare = 1;
endfunction: compare


function int unsigned TR::byte_size(int kind = -1);
   // ToDo: Implement this method

endfunction: byte_size


function int unsigned TR::byte_pack(ref logic [7:0] bytes[],
                                    input int unsigned offset = 0,
                                    input int kind = -1);
   // ToDo: Implement this method
 
endfunction: byte_pack


function int unsigned TR::byte_unpack(const ref logic [7:0] bytes[],
                                      input int unsigned offset = 0 ,
                                      input int len = -1    , 
                                      input int kind = -1  );
   // ToDo: Implement this method

endfunction: byte_unpack

NORMAL_END
`vmm_channel(TR)
`vmm_atomic_gen(TR, "TR")
`vmm_scenario_gen(TR, "TR")

`endif // TR__SV
