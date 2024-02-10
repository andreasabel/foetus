(* Hooks for the semantic actions of the parser. *)

val do_term = ref (fn (_ : Tm) => () );
val do_defs = ref (fn (_ : Defs) => () );
