/***************************************************************************
*******************************************************************************
*
* This test shows how to run a trivial test
* to debug the environment and the DUT
*
*******************************************************************************
*/


program test (fpu_i iport);

`include "vmm.sv"
`include "fpu.sv"
`include "env.sv"

    // Top level environment
    env the_env = new(iport);

    initial begin
   
       //the_env.log.set_verbosity(the_env.log.TRACE_SEV);

       // Run for only 1 scenario
       the_env.gen_cfg();
       the_env.cfg.run_for = 1000;

       // Kick off the test
        the_env.run();
    end

endprogram
