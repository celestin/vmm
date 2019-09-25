//
// Template for VMM-compliant testcase
// <TR>          Name of the transaction class
// <TEST_NAME>   Name of test case
// [filename]    TEST_NAME
//

class TR_write extends TR;

   `vmm_typename(TR_write)
   constraint cst_write_test {
      kind == WRITE;
      status == IS_OK;
   }
   MACRO_START
   `vmm_data_member_begin(TR_write)
   `vmm_data_member_end(TR_write)
   MACRO_END
   NORMAL_START
   function vmm_data allocate();
      TR_write tr = new(this.get_object_name(), get_parent());
      allocate = tr;
   endfunction: allocate
   
   function vmm_data copy(vmm_data cpy = null);
      TR_write to;
   
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
   NORMAL_END 
 
   `vmm_class_factory(TR_write)

endclass: TR_write


class TEST_NAME extends vmm_test;

   `vmm_typename(TEST_NAME)

   function new(string name);
      super.new(name);
   endfunction: new

   virtual function void set_config();
      //ToDo : Add configuration override construct here
   endfunction

   virtual function void build_ph();
	   
   endfunction

   virtual function void start_of_sim_ph();
      super.start_of_sim_ph();
      //ToDo: Change the path of the Generator based on the env arhchitecture
      TR::override_with_new("@env:atmc_gen:randomized_obj",TR_write::this_type , log);
   endfunction : start_of_sim_ph

   virtual function void start_of_test_ph();
	   
   endfunction

endclass: TEST_NAME

TEST_NAME tst2 = new("TEST_NAME");
