(*
** closure.sml -- Types that may not be recompiled
**
** by Andreas Abel, Thorsten Altenkirch
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
*)

(* Terms *)
datatype Tm =
    t_var of string
  | t_lam of string*Tm
  | t_app of Tm*Tm
  | t_c of string*Tm
  | t_case of Tm*(Pat list)
  | t_tup of (string*Tm) list
  | t_dot of Tm*string
  | t_let of Defs*Tm
withtype Pat = string*(string*Tm)
and Defs = (string*Tm) list;

(* Closure/Environment *)
datatype Entry =
    e_val of string * (Tm * Entry list) (*Clos*)
  | e_rec of Defs
  | e_gen of string*int;
type Env = Entry list;
type Clos = Tm*Env;

(* SML/NJ also understands this, but not MLton: https://github.com/MLton/mlton/issues/548
datatype Entry =
    e_val of string*Clos
  | e_rec of Defs
  | e_gen of string*int
withtype Env = Entry list
and Clos = Tm*Env;
*)

val globalEnv = ref ([]: Env);
