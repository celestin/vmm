typedef class scoreboard;
class RcvSbCallbacks extends Receiver_callbacks;

   // Lab 3 - Add an instance of the scoreboard
   // ToDo
   scoreboard sb;


   // Lab 3 - Create a constructor which accepts a scoreboard via the argument
   // ToDo
   function new(scoreboard sb);
      this.sb = sb;
   endfunction


   // Lab 3 - Implement post_trans callback method to pass transaction to scoreboard
   // ToDo
   function void post_trans(Receiver xactor, Packet tr);
      this.sb.check(tr);
   endfunction

endclass
