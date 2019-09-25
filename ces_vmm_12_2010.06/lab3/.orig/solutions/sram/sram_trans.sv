class sram_trans extends vmm_data;
   `vmm_typename(sram_trans)

   typedef enum bit {READ = 1'b1, WRITE =  1'b0} kind_e;

   rand bit [31:0] address;
   rand bit [7:0]  data;
   rand kind_e    kind;

   `vmm_data_member_begin(sram_trans)
      `vmm_data_member_scalar(address, DO_ALL)
      `vmm_data_member_scalar(data, DO_ALL)
      `vmm_data_member_enum(kind, DO_ALL)
   `vmm_data_member_end(sram_trans)

   `vmm_class_factory(sram_trans)
endclass

`vmm_channel(sram_trans)
