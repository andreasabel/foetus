(*
** top.sml
**
** by Andreas Abel, Thorsten Altenkirch
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** The top-level functions have been put in a separate file for debugging
** speedup. If you have modified e.g. check.sml, just compile check.sml and
** start.sml. This will recompile the top level functions, thus the new check
** routines will be used in the foetus run.
*)

(****************************** Top level ******************************)

fun doTerm t =
    (
     (* print ("doTerm: "^(printExpr t)^"\n"); *)
     print ("result: "^(printValue (nf (t, !globalEnv)))^"\n")
     )
    handle Error s => print ("Error : "^s^"\n");

fun doDefs (defs) =
    (
     (* print ("doDefs  "^(printDefs defs)^"\n"); *)
     checkDefs (!globalEnv, defs);
     globalEnv := (e_rec defs) :: !globalEnv
     )
    handle Error s => print ("Error : "^s^"\n");

fun foetus () =
    (do_term := doTerm;
     do_defs := doDefs;
     print (version^"\n");
     parseStream true stdIn)
    handle Error s => print ("Error : "^s^"\n");

fun foetusFile fileName =
    (do_term := doTerm;
     do_defs := doDefs;
     print (version^"\n");
     print("[Opening file " ^ fileName ^ "]\n");
     parseStream false (TextIO.openIn fileName);
     print("[Closing file " ^ fileName ^ "]\n")
    )
    handle Error s => print ("Error : "^s^"\n");

fun main (_, [fileName]) = (foetusFile(fileName); OS.Process.success)
  | main (_, [])         = (foetus(); OS.Process.success)
  | main _               = (print "syntax: foetus [file]\n"; OS.Process.failure);
