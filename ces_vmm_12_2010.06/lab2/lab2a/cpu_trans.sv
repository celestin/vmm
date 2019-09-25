class cpu_trans extends vmm_data;
   `vmm_typename(cpu_trans)

   typedef enum bit {READ = 1'b1, WRITE =  1'b0} kind_e;
   typedef enum {IS_OK, ERROR} status_e;
   rand kind_e    kind;
   rand status_e status;   

   // Lab 2a - Add new class new members for the CPU transaction
   // ToDo


   constraint cpu_trans_valid {
      status == IS_OK;
      // Lab 2a - Add new constraints for the generation of a valid CPU transaction
      // ToDo

   }

   // Lab 2a - Use VMM shorthand macros to create class methods
   // ToDo


   function void post_randomize();
     `vmm_debug(this.log, this.psdisplay("cpu_trans post_randomize "));
   endfunction

   `vmm_class_factory(cpu_trans)
endclass
`vmm_channel(cpu_trans)
`vmm_atomic_gen(cpu_trans, "CPU trans atomic generator")
`vmm_scenario_gen(cpu_trans, "CPU trans scenario generator")
