typedef class Packet_atomic_gen;
// Lab 3 - Create Packet_atomic_gen_callbacks class
// ToDo
class Packet_atomic_gen_callbacks extends vmm_xactor_callbacks;
   virtual task post_inst_gen(Packet_atomic_gen gen, Packet obj, ref bit drop);
   endtask
endclass

class Packet_atomic_gen extends vmm_xactor;
  int scenario_count, obj_count, stop_after_n_insts;
  typedef enum int {GENERATED, DONE} symbols_e;

  Packet         randomized_obj;
  Packet_channel out_chan;

  function new(string instance = "class", int stream_id = -1, Packet_channel out_chan = null);
    super.new("Packet_atomic_gen", instance, stream_id);
    this.randomized_obj = new();
    if (out_chan == null) out_chan = new(("Generator output channel"), instance);
    this.out_chan  = out_chan;
    this.notify.configure(GENERATED, vmm_notify::ONE_SHOT);
    this.notify.configure(DONE, vmm_notify::ON_OFF);
    this.stop_after_n_insts = 0;
    this.scenario_count = 0;
  endfunction

  virtual protected task main();
    super.main();

    this.obj_count = 0;

    while ((this.obj_count < this.stop_after_n_insts) || (stop_after_n_insts <= 0)) begin
      Packet obj;
      this.wait_if_stopped();
      this.randomized_obj.stream_id = stream_id;
      this.randomized_obj.scenario_id = scenario_count;
      this.randomized_obj.data_id = obj_count;

      if (!randomized_obj.randomize()) begin
        `vmm_error(this.log, "Cannot randomize atomic instance");
        continue;
      end
      $cast(obj, randomized_obj.copy());
      begin
        bit drop = 0;

        // Lab 3 - insert callback method post_int_gen()
        // ToDo
        `vmm_callback(Packet_atomic_gen_callbacks, post_inst_gen(this, obj, drop));


        if (!drop) begin
          out_chan.put(obj);
          obj_count++;
          this.notify.indicate(GENERATED, obj);
        end
      end
    end

    this.notify.indicate(DONE);
    this.notify.indicate(vmm_xactor::XACTOR_STOPPED);
    this.notify.indicate(vmm_xactor::XACTOR_IDLE);
    this.notify.reset(vmm_xactor::XACTOR_BUSY);
    this.scenario_count++;
  endtask

endclass
