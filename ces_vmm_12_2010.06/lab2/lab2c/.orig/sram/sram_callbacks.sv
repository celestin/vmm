// Lab 2c - Extend the sram_model_callbacks
class sram_callbacks extends sram_model_callbacks;

   virtual task post_trans(sram_model bfm, sram_trans tr);
      // Lab 2c - Inserting a log display after the sram_model prcess a transaction
      // ToDo

   endtask

endclass
