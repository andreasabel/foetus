(* FOETUS
** Funktionale, - obgleich eingeschraenkt - Termination untersuchende Sprache
**
** foetus.sml
**
** by Andreas Abel, Thorsten Altenkirch
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** the BODY of foetus
**
** - data structures for terms (Tm), enviroments (Env), closures (Clos)
**   (moved to closure.sml)
** - values
** - functions for evaluation of terms (hnf)
*)

(* Value *)
datatype Val =
    v_c of string*Val
  | v_tup of (string*Val) list
  | v_lam of string*Clos
  | v_app of Val*Clos
  | v_case of Val*(Pat list)*Env
  | v_gen of string*int
  | v_c_lazy of string*Clos
  | v_tup_lazy of (string*Tm) list*Env
  | v_dot of Val*string
  | v_let of Defs*Tm*Env (* lazy let required for analyse *)
  | v_def of Clos        (* lazy env-lookup *);

(* creating unique identifers *)

val curId = ref 0;
fun newGen() = (curId := !curId + 1; !curId);
fun addGen(x,env) = e_gen(x,newGen())::env;

(*
val cur_par = ref 0;
fun new_gen (x) =
    if x="" then ""
    else (cur_par := !cur_par + 1;
          x^"_"^(Int.toString (!cur_par)));
fun addGen(x,env) = e_gen(x,new_gen(x))::env;
*)

exception Error of string;


(* hnf (Head Normal Form) : Tm * Env -> Val
** nf  (Normal Form) :      Tm * Env -> Val
**
**
** The switch "lazy"
**
** matters only within hnf_var (variable lookup) resp. when considering a "let"
** and specifies whether to return the body of a defined function and unfold
** it further or just to return the identifier to prevent unfolding resp.
** whether to add the "let" as e_rec to the environment or return the whole
** "let" for further processing. E.g.
**
** add  = [x][y]case x of { O o => y   | S x' => S(add x' y)};
** mult = [x][y]case x of { O o => O() | S x' => add y (mult x' y) }
**
** While analysing mult unfolding of add is undesirable because we want to
** extract the call mult->add. We do not know the values of x and y and it
** would lead to infinite unfolding.
** But when evaluating e.g. "mult (S(S(O()))) (S(S(O())))" unfolding is
** required to reach normal form (nf).
**
** v_c vs. v_c_lazy resp. v_tup vs. v_tup_lazy
**
** hnf always returns the "lazy" versions of v_c and v_tup, it does not look
** what is within the constructor (v_c) or tupel (v_tup). nf takes the
** contents of v_c_lazy and v_tup_lazy and evaluates them further.
**
**
** abbreviations:
**
** rho : Env
** t,s : Tm
** x   : string (Variable)
** c   : string (Constant)
** cts : (string*Tm) list (Tupel)
** v   : Value
*)

fun hnf' lazy (t_var x, rho)      = hnf_var  lazy (x,rho)
  | hnf' lazy (t_app (t,s),rho)   = hnf_app  lazy (hnf' lazy (t,rho),(s,rho))
  | hnf' lazy (t_case (t,ps),rho) = hnf_case lazy (hnf' lazy (t,rho),ps,rho)
  | hnf' lazy (t_dot (t,c),rho)   = hnf_dot  lazy (hnf' lazy (t,rho),c)
  | hnf' lazy (t_let (xts,t),rho) =
      if lazy then v_let(xts,t,rho) (* today we are very lazy! *)
      else hnf' lazy (t,e_rec(xts)::rho)
  | hnf' lazy (t_lam (x,t),rho)   = v_lam (x,(t,rho))
  | hnf' lazy (t_c (c,t),rho)     = v_c_lazy (c,(t,rho))
  | hnf' lazy (t_tup cts,rho)     = v_tup_lazy (cts,rho)

and hnf_var lazy (x,[]) = raise Error ("hnf_var: Undefined variable : "^x)
  | hnf_var lazy (x,rho as (e_gen(p as (y,i)))::rho') =
       if (x=y) then v_gen p
       else hnf_var lazy (x, rho')
           (* generic variable *)
  | hnf_var lazy (x,(e_val (y,cl))::rho) =
       if x=y then hnf' lazy cl
       else hnf_var lazy (x,rho)
           (* bound variable *)
  | hnf_var lazy (x,rho as (e_rec xts)::rho') =
       let val t = assoc (x,xts)
       in (if lazy then v_def(t,rho)   (* lazy lookup *)
           else hnf' lazy (t,rho))
       end
       handle Assoc => hnf_var lazy (x,rho')
           (* defined variable *)

and hnf_app lazy (v_lam (x,(t,rho)),cl) = hnf' lazy (t,e_val (x,cl)::rho)
  | hnf_app lazy (v,cl) = v_app (v,cl)
      (*raise Error "hnf_app: not a function" *)

and hnf_case lazy (v_c_lazy (c,(t,rho')),ps,rho) =
       let val (x,u) = assoc (c,ps)
                        handle Assoc =>
                            raise Error "hnf: case not matched"
       in hnf' lazy (u,(e_val (x,(t,rho')))::rho)
       end
  | hnf_case lazy (v,ps,rho) = v_case(v,ps,rho)
       (* raise Error "hnf_case: not a constructor" *)

and hnf_dot lazy (v_tup_lazy (cts,rho),c) =
       ((hnf' lazy (assoc (c,cts),rho))
        handle Assoc => raise Error "hnf: label not defined")
  | hnf_dot lazy (v,c) = v_dot(v,c)
       (* raise Error "hnf_dot: not a tuple"; *)

fun hnf cl = hnf' true cl;
fun hnf_eager cl = hnf' false cl

fun nf (t,rho) =
    (case hnf_eager (t,rho) of
         v_c_lazy (c,(t,rho)) => v_c (c,nf (t,rho))
       | v_tup_lazy (cts,rho) => v_tup (map (fn (c,t) => (c,nf (t,rho))) cts)
       | v => v);


(****************************** print ******************************)

val unprintable = "...";

fun printList _ [] = ""
  | printList _ [str] = str
  | printList separator (str::strs) = str^separator^(printList separator strs);

(* Terms resp. Expressions *)

fun printExpr (t_c (const, arg as (t_tup _))) = const^(printExpr arg)
  | printExpr (t_c (const, arg)) = const^"("^(printExpr arg)^")"
  | printExpr (t_tup defs) = "("^(printDefs defs)^")"
  | printExpr (t_dot (t,c)) = (printExpr t)^"."^c
  | printExpr (t_var x) = x
  | printExpr (t_lam (x, term)) = "(["^x^"]"^(printExpr term)^")"
  | printExpr (t_app (lterm, rterm)) = "("^(printExpr lterm)^" "^
      (printExpr rterm)^")"
  | printExpr (t_case (term, patterns)) = "case "^(printExpr term)^" of {"^
      (printPatterns patterns)^"}"
  | printExpr (t_let (defs, t)) = "let "^(printDefs defs)^" in "^(printExpr t)
(*  | printExpr _ = unprintable
*)
and printPatterns p =
      let fun printPattern (const,(var,term)) = const^" "^var^" => "^
          (printExpr term)
      in printList "|" (map printPattern p)
      end

and printDef (ident, expr) = ident^"="^(printExpr expr)
and printDefs' sep identExprList = printList sep (map printDef identExprList)
and printDefs defs = printDefs' "," defs;

(* Environments *)

fun printEntry (e_val (x, (t, env))) = x^"="^(printExpr t)^(printEnv env)
  | printEntry (e_gen (x, i)) = x^"=?"
  | printEntry (e_rec defs) = printDefs defs

and printEnv [] = ""
  | printEnv (env as (entry::env'))= if (env = !globalEnv) then ""
      else "{"^(printEntry entry)^(printEnv' env')^"}"

and printEnv' [] = ""
  | printEnv' (env as (entry::env'))= if (env = !globalEnv) then ""
      else ","^(printEntry entry)^(printEnv' env');
(*
and printEnv env = if (env = !globalEnv) then ""
      else "{"^(printList "," (map printEntry env))^"}";
*)
fun printClos (t, env) = (printExpr t)^(printEnv env);

(* Values *)

fun printValue (v_c (const, arg as (v_tup _))) = const^(printValue arg)
  | printValue (v_c (const, arg)) = const^"("^(printValue arg)^")"
  | printValue (v_tup defs) = "("^(printList ", " (map printVDef defs))^")"
  | printValue (v_lam (x, cl)) = "["^x^"]"^(printClos cl)
  | printValue (v_app (v, cl)) = "("^(printValue v)^" "^(printClos cl)^")"
  | printValue (v_case(v, ps, cl)) = "case "^(printValue v)^" of {"^
      (printPatterns ps)^"}"
  | printValue (v_gen(x,i)) = x
  | printValue (v_dot (v, c)) = (printValue v)^"."^c
  | printValue (v_c_lazy (c, cl)) = c^"("^(printClos cl)^")"
  | printValue (v_tup_lazy(cts, env)) = "("^(printList ", " (map printDef cts))
      ^")"^(printEnv env)
  | printValue _ = unprintable

and printVDef (ident, expr) = ident^"="^(printValue expr);

