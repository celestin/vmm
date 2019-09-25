function string test_cfg::psdisplay(string prefix = "");
   int cnt = 0;
   $sformat(psdisplay, "%s run_for_n_packets = %0d\n", prefix, run_for_n_packets);
   $sformat(psdisplay, "%s%s num_of_iports = %0d\n", psdisplay, prefix, num_of_iports);
   $sformat(psdisplay, "%s%s num_of_oports = %0d\n", psdisplay, prefix, num_of_oports);
   $sformat(psdisplay, "%s%s valid inputs ports:  ", psdisplay, prefix);
   for (int i=0; i<iports_in_use.size; i++) begin
      if (iports_in_use[i])
         if (++cnt == iports_in_use.sum()) begin
            $sformat(psdisplay, "%s 'h%0h", psdisplay, i);
            break;
         end else $sformat(psdisplay, "%s 'h%0h, ", psdisplay, i);
   end
   $sformat(psdisplay, "%s%s\n valid outputs ports: ", psdisplay, prefix);
   cnt = 0;
   for (int i=0; i<oports_in_use.size; i++) begin
      if (oports_in_use[i])
         if (++cnt == oports_in_use.sum()) begin
            $sformat(psdisplay, "%s 'h%0h", psdisplay, i);
            break;
         end else $sformat(psdisplay, "%s 'h%0h, ", psdisplay, i);
   end
endfunction
