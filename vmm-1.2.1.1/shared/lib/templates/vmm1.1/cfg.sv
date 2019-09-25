//
// Template for VMM-compliant configuration class
// <CFG>        Name of configuration class
//

`ifndef CFG__SV
`define CFG__SV


class CFG extends vmm_data; 

   // Define test configuration parameters (e.g. how long to run)
   int num_trans = 1;
   int num_scen = 1;
   
   typedef enum bit [1:0] {NORMAL, RECORD, PLAYBACK} mode_e;
   mode_e mode = NORMAL;
   
   NORMAL_START
   static vmm_log log = new("CFG", "class");
   NORMAL_END
   MACRO_START
   `vmm_data_member_begin(CFG)
      `vmm_data_member_enum(mode, DO_ALL)
      `vmm_data_member_scalar(num_trans, DO_ALL)
      `vmm_data_member_scalar(num_scen, DO_ALL)
      // ToDo: add properties using macros here

   `vmm_data_member_end(CFG)

   MACRO_END
   NORMAL_START
   // ToDo: Add constraint blocks to prevent error injection
   extern function new();
   extern virtual function string psdisplay(string prefix = "");
   extern virtual function bit is_valid(bit silent = 1,
                                        input int kind = -1);
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
endclass: CFG
NORMAL_START

function CFG::new();
   string md;
   vmm_opts opts;
   super.new(this.log);
   opts = new();
   md = opts.get_string("MODE", "NORMAL", "Specifies the mode");
   case (md)
     "NORMAL"   : mode = NORMAL;
     "RECORD"   : mode = RECORD;
     "PLAYBACK" : mode = PLAYBACK;
   endcase
   num_trans = opts.get_int("NUM_TRANS", num_trans, "Num Of transactions");
   num_scen  = opts.get_int("NUM_SCEN", num_scen, "Num Of scenarios");
endfunction: new


function string CFG::psdisplay(string prefix = "");

    // ToDo: Implement this method
    psdisplay = $psprintf("%s Transactions = %0d Scenarios = %0d", prefix, num_trans,num_scen);
endfunction: psdisplay


function bit CFG::is_valid(bit silent = 1,
                          input int kind = -1);

 // ToDo: Implement this method

endfunction: is_valid


function vmm_data CFG::allocate();
   
   CFG tr = new;
   allocate = tr;

endfunction: allocate


function vmm_data CFG::copy(vmm_data cpy = null);
   
   CFG to;

   // Copying to a new instance?
   if (cpy == null) 
      to = new;
    else 
      // Copying to an existing instance. Correct type?
      if (!$cast(to, cpy)) begin 
         `vmm_fatal(this.log, "Attempting to copy to a non CFG instance");
         return null;
     end 

   super.copy_data(to);

   to.mode = this.mode;
   to.num_trans = this.num_trans;
   to.num_scen  = this.num_scen;
   // ToDo: Copy additional class properties

   copy = to;  
  
endfunction: copy


function bit CFG::compare(vmm_data   to,
                         output string diff,
                         input int  kind = -1);
   
   CFG tr;
    
   compare = 0;
   if (to == null) begin 
      `vmm_fatal(this.log, "Cannot compare to NULL instance");
      return 0;
   end

   if (!$cast(tr,to)) begin 
      `vmm_fatal(this.log, "Attempting to compare to a non CFG instance");
      return 0;
   end
    if (this.mode != tr.mode) begin
      $sformat(diff, "Mode %0s != %0s", this.mode, tr.mode);
      return 0;
   end
   if (this.num_trans != tr.num_trans || this.num_scen !=tr.num_scen) begin
      diff = $psprintf("Total Transaction %0d != %0d Scearios %0d != %0d", this.num_trans, tr.num_trans,this.num_scen,tr.num_scen);
      return 0;
   end
   // ToDo: Compare additional class properties

   compare = 1;

endfunction: compare


function int unsigned CFG::byte_size(int kind = -1);
   
   // ToDo: Implement this method

endfunction: byte_size


function int unsigned CFG::byte_pack(ref logic [7:0] bytes[],
                                    input int unsigned offset = 0,
                                    input int kind = -1);
    
   // ToDo: Implement this method
 
endfunction: byte_pack


function int unsigned CFG::byte_unpack(const ref logic [7:0] bytes[],
                                      input int unsigned offset = 0 ,
                                      input int len = -1, 
                                      input int kind = -1);

   // ToDo: Implement this method

endfunction: byte_unpack
NORMAL_END


`vmm_channel(CFG)
`vmm_atomic_gen(CFG, "CFG Gen")
`vmm_scenario_gen(CFG, "CFG")

`endif // CFG__SV
