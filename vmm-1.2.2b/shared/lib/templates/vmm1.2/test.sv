//
// Template for VMM-compliant testcase
// <TEST_NAME>   Name of test case
// [filename]    TEST_NAME
//

//Error Injection Callbacks
class XACT_err_callbacks extends XACT_callbacks;

   FULL_DUPLEX_FNC_BFM_START
   // Called before a transaction has been executed by functional driver
   virtual task pre_ex_trans(XACT xactor,
                             TR tr,
                             ref bit drop);
    if(!drop) begin
        //ToDo: Add the Error Injection logic to modify the transaction tr, if needed
    end   
   endtask: pre_ex_trans
   FULL_DUPLEX_FNC_BFM_END
   FULL_DUPLEX_PHY_BFM_START
   // Called before a transaction has been executed by physical driver
   virtual task pre_trans(XACT xactor,
                          TR tr,
                          ref bit drop);
   if(!drop) begin
        //ToDo: Add the Error Injection logic to modify the transaction tr, if needed
    end   
   endtask: pre_trans
   FULL_DUPLEX_PHY_BFM_END

endclass : XACT_err_callbacks

TST_IMPL_START
//Test class TEST_NAME
class TEST_NAME extends vmm_test;
   `vmm_typename(TEST_NAME)

   //Instantiating Error Injection callback, ToDo: Instantiates other callbacks if any
   XACT_err_callbacks xct_err_inj_cb=new(); 

   function new(string name);
      super.new(name);
   endfunction: new

   virtual function void build_ph();
   endfunction: build_ph

   virtual function void start_of_sim_ph();
     super.start_of_sim_ph();
     //registering the error injection callback before scoreboard callbacks to keep the scoreboard 'aware' of Errors. 
     //ToDo: Append/Prepend other callbacks if required
     SUBENV_EN_START
     SING_DRV_START
     env.mast_subenv.driver.prepend_callback(xct_err_inj_cb); 
     SING_DRV_END
     MULT_DRV_START
     env.mast_subenv.driver_0.prepend_callback(xct_err_inj_cb);        
     MULT_DRV_END
     SUBENV_EN_END
     SUBENV_DIS_START
     SING_DRV_START
     env.driver.prepend_callback(xct_err_inj_cb);
     SING_DRV_END
     MULT_DRV_START
     env.driver_0.prepend_callback(xct_err_inj_cb);  
     MULT_DRV_END
     SUBENV_DIS_END
      //ToDo: Set the the testcase-specific configuration,  Add factory override statements
   endfunction : start_of_sim_ph

endclass: TEST_NAME

TEST_NAME tst1 = new("TEST_NAME");
TST_IMPL_END

TST_EXPL_START

`vmm_test_begin(TEST_NAME, ENV, "TEST_NAME")
   //Instantiating Error Injection callback, ToDo: Instantiates other callbacks if any
   XACT_err_callbacks xct_err_inj_cb=new(); 
   // ToDo: Set configuration parameters and turn rand mode OFF, if needed
   env.build();
      
   //registering the error injection callback before scoreboard callbacks to keep the scoreboard 'aware' of Errors. 
   //ToDo: Append/Prepend other callbacks if required
   SUBENV_EN_START
   SING_DRV_START
   env.mast_subenv.driver.prepend_callback(xct_err_inj_cb); 
   SING_DRV_END
   MULT_DRV_START
   env.mast_subenv.driver_0.prepend_callback(xct_err_inj_cb);        
   MULT_DRV_END
   SUBENV_EN_END
   SUBENV_DIS_START
   SING_DRV_START
   env.driver.prepend_callback(xct_err_inj_cb);
   SING_DRV_END
   MULT_DRV_START
   env.driver_0.prepend_callback(xct_err_inj_cb);        
   MULT_DRV_END
   SUBENV_DIS_END


   // ToDo: Set message service interface verbosity, if needed

   // ToDo: Replace factory instances, if needed

   env.start();
  
   begin
      MULT_DRV_START
      // For multiple driver, set total number of transaction for all driver
      // `foreach_vmm_xactor(XACT, "/./", "/./") begin
      // xact.stop_after_n_insts = 3;
      // end
      MULT_DRV_END
      // ToDo: Directed stimulus, if needed
   end
   
   env.run();
`vmm_test_end(TEST_NAME)
TST_EXPL_END
