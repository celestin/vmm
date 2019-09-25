#
# Template for RALF file used by RAL environment
// <VNAME>   Name of VIP
#

# ToDo: VNAME.ralf file needs to be modified according to user configuration 
# to generate ral_VNAME block inside ral_VNAME.sv file
# Default implementation of register, memory, field and block 
# kept inside this VNAME.ralf file

block VNAME {
   bytes 4;
   register CHIP_ID @'h0000 {
      field REVISION_ID {
         bits 8;
         access ro;
         reset 'h03;
      }
      field CHIP_ID {
         bits 8;
         access ro;
         reset 'h5A;
      }
      field PRODUCT_ID {
         bits 10;
         access ro;
         reset 'h176;
      }
   }
  
   memory VNAME_RAM @'h0800 {
      size 1k;
      bits 32;
      access rw;
   }
}
