typedef class scoreboard;
class GenSbCallbacks extends Packet_atomic_gen_callbacks;
   scoreboard sb;
   function new(scoreboard sb);
      this.sb = sb;
   endfunction
   task post_inst_gen(Packet_atomic_gen gen, Packet obj, ref bit drop);
      this.sb.deposit(obj);
//      this.sb.check(obj);
   endtask
endclass
