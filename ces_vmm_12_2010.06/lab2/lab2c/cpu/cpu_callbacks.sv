// Lab 2c - Extend the cpu_driver_callbacks
class cpu_callbacks extends cpu_driver_callbacks;

   virtual task post_trans(cpu_driver drv, cpu_trans tr);
      // Lab 2c - Inserting a log display after the cpu_driver drives a transaction
      // ToDo

   endtask

endclass
