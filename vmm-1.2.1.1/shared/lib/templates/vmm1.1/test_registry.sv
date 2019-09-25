//
// Template for VMM-compliant Program block
// <PB>         Name of the program block
// <ENV>        Name of environment 
// <IF>         Name of physical interface
//

`ifndef PB__SV
`define PB__SV

`include "IF.sv"

SING_DRV_START
program PB(IF intf);
SING_DRV_END
MULT_DRV_START
program PB(IF intf [INTF_COUNT]);
MULT_DRV_END

`include "ENV.sv"
`include "TEST_NAME.sv"
 // ToDo: Include test list here

   ENV env_inst;
   MACRO_START
   vmm_test_registry registry;
   MACRO_END
   initial begin
      env_inst = new(intf);
      MACRO_START
      registry = new;
      registry.run(env_inst);
      MACRO_END
      NORMAL_START
      env_inst.run();
      NORMAL_END
   end

endprogram: PB

`endif // PB__SV

