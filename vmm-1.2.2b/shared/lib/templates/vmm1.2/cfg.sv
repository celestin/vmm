//
// Template for VMM-compliant configuration class
// <CFG>        Name of configuration class
//

`ifndef CFG__SV
`define CFG__SV

class CFG extends vmm_data; 

   `vmm_typename(CFG)
   
   NORMAL_START
   static vmm_log log = new("CFG","object");

   NORMAL_END
   typedef enum bit [1:0] {NORMAL, RECORD, PLAYBACK} mode_e;
   mode_e mode = NORMAL;
   // Define test configuration parameters (e.g. how long to run)
   rand int num_trans;
   rand int num_scen;
   // ToDo: Add other environment configuration varaibles

   constraint cst_num_trans_default {
      num_trans inside {[1:7]};
   }
   constraint cst_num_scen_default {
      num_scen inside {[1:2]};
   }
   // ToDo: Add constraint blocks to prevent error injection
   MACRO_START
 
   `vmm_data_member_begin(CFG)
      `vmm_data_member_scalar(num_trans, DO_COPY | DO_PRINT)
      `vmm_data_member_scalar(num_scen, DO_COPY | DO_PRINT)
      `vmm_data_member_enum(mode, DO_COPY | DO_PRINT)
      // ToDo: add properties using macros here

   `vmm_data_member_end(CFG)
   MACRO_END

   extern function void pre_randomize();
   NORMAL_START
   extern function new(string inst = "", vmm_object parent = null);
   extern virtual function string psdisplay(string prefix = "");
   extern virtual function CFG allocate();
   extern virtual function CFG copy(vmm_data cpy = null);
   NORMAL_END 
  
   `vmm_class_factory(CFG)

endclass: CFG


function void CFG::pre_randomize();
   bit is_set;
   string md;

   num_trans = vmm_opts::get_object_int(is_set, this, "NUM_TRANS", 3, "SET num_trans value");
   if (is_set) 
     num_trans.rand_mode(0);
   else 
    `vmm_note(log, "num_trans was NOT set through vmm_opts,Randomizing it");

   num_scen= vmm_opts::get_object_int(is_set, this, "NUM_SCN", 3, "SET num_scen value");
   if (is_set) 
     num_scen.rand_mode(0);
   else 
    `vmm_note(log, "num_scen was NOT set through vmm_opts,Randomizing it");

   md = vmm_opts::get_object_string(is_set,this,"MODE", "NORMAL", "Specifies the mode");
   case (md)
      "NORMAL"   : mode = NORMAL;
      "RECORD"   : mode = RECORD;
      "PLAYBACK" : mode = PLAYBACK;
   endcase
   if (!is_set) 
     `vmm_warning(log, "mode was NOT set through vmm_opts");
   //ToDo: get other object class properties if added later/requied

endfunction: pre_randomize
NORMAL_START


function CFG::new(string inst = "", vmm_object parent = null);
   super.new(this.log);
   this.set_parent_object(parent);
endfunction: new


function string CFG::psdisplay(string prefix = "");
   psdisplay = { $psprintf("\t************** CFG ***************\n"),
                 $psprintf("\tnum_trans  : %0d\n", num_trans),
                 $psprintf("\tmode       : %s\n", mode.name()),
                 $psprintf("\t**********************************\n")
               };
   //ToDo: Add another class properties to psdisplay if added later.

endfunction: psdisplay


function CFG CFG::allocate();
   allocate = new(this.get_object_name(), get_parent_object());
endfunction: allocate


function CFG CFG::copy(vmm_data cpy = null);
   CFG to;

   // Copying to a new instance?
   if (cpy == null) 
      to = new(this.get_object_name(), get_parent());
    else 
      // Copying to an existing instance. Correct type?
      if (!$cast(to, cpy)) begin 
         `vmm_fatal(this.log, "Attempting to copy to a non CFG instance");
         return null;
     end 

   super.copy_data(to);

   to.num_trans = this.num_trans;
	to.mode      = this.mode;

   // ToDo: Copy additional class properties

   copy = to;
endfunction: copy
NORMAL_END

`endif // CFG__SV
