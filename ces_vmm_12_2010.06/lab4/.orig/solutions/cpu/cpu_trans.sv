class cpu_trans extends vmm_data;
   `vmm_typename(cpu_trans)

   typedef enum bit {READ = 1'b1, WRITE =  1'b0} kind_e;
   typedef enum {IS_OK, ERROR} status_e;
   rand status_e status;   
   rand kind_e    kind;

   // Lab 2a - Add new class new members for the CPU transaction
   rand bit [31:0] address;
   rand bit [7:0]  data;
   rand bit [3:0]  trans_delay;

   constraint cpu_trans_valid {
      status == IS_OK;
      // Lab 2a - Add new constraints for the generation of a valid CPU transaction
      address inside { [0:((4*256)-1)] };
      trans_delay < 10;
   }

   // Lab 2a - Use VMM shorthand macros to create class methods
   `vmm_data_member_begin(cpu_trans)
      `vmm_data_member_scalar(address, DO_ALL)
      `vmm_data_member_scalar(data, DO_ALL)
      `vmm_data_member_scalar(trans_delay, DO_ALL-DO_COMPARE)
      `vmm_data_member_enum(kind, DO_ALL)
   `vmm_data_member_end(cpu_trans)

   function void post_randomize();
      `vmm_debug(this.log, this.psdisplay("cpu_trans post_randomize "));
   endfunction

   `vmm_class_factory(cpu_trans)
endclass

`vmm_channel(cpu_trans)
`vmm_atomic_gen(cpu_trans, "CPU trans atomic generator")
`vmm_scenario_gen(cpu_trans, "CPU trans scenario generator")
