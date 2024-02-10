(*
** analyse.sml
**
** by Andreas Abel
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** the HEART of foetus. Extracts function applications out of the given
** definitions and builds dependecies (<, +, ?) between variables
** (identifiers).
*)

(*
use "matrix.sml";
open List; (* SML 97 *)
*)

val debug = ref false;
val verbose = ref true;

(****************************** Identifier type **************************
**
** internally an identifier is stored as an integer for efficiency reasons.
** For readable output the original name is required: Therefore ExtIdent
** stores it with the integer value
*)

type Ident = int;
val emptyIdent : Ident = 0
fun identToString i = Int.toString i;

type ExtIdent = string * Ident;
val emptyExtIdent : ExtIdent = ("", emptyIdent);
fun extIdentToString (name,i) = name; (* TODO! *)

(****************************** Dependencies *****************************
**
** structure for storing dependencies (<, =) between variable. Dependencies
** result from case-statements, e.g.
**
** f = [x] ... case x of { S x' => ...
**
** Here x' < x, thus call addLess(x',x). After second call addLess(x'',x')
** the query getRel(x'',x) would result in rel_less (transitivity).
** In case of
**
** f = [x] ... let y = x in ...
**
** you could use addEqual(y,x), but analyse does not recognize this equality
** yet.
*)

datatype Relation = rel_less | rel_equal | rel_unknown;

fun printRel rel_less = "<"
  | printRel rel_equal = "="
  | printRel rel_unknown = "?";

signature DEPENDENCIES = sig
    type Dependencies;

    val empty  :  Dependencies;
    val addLess:  Dependencies * Ident * Ident -> Dependencies;
      (* adds the dependency #1 < #2 *)
    val addEqual: Dependencies * Ident * Ident -> Dependencies;
      (* adds the synonym    #1 = #2 *)
    val getRel:   Dependencies * Ident * Ident -> Relation;
      (* returns rel_less    if #1 < #2
                 rel_equal   if #1 = #2
                 rel_unknown else     *)
end;

(*
** Inlined: simpledeps.sml
**
** by Andreas Abel
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** very simple implementation of DEPENDENCIES; getRel has complexity O(n^2)
**
** limitations:
** a) no equalities
** b) limited, but sufficient transitivity (depends on the insertion order):
**    From b < a, c < b it concludes c < a,
**    from c < b, b < a it does not conclude c < a however.
**
** SML example:
**
** correct order: (transitivity)
**   - val deps = addLess(addLess(empty,2,3),1,2);
**   val deps = [(1,[2,3]),(2,[3])] : Dependencies
** incorrect order: (no transitivity)
**   - val deps = addLess(addLess(empty,1,2),2,3);
**   val deps = [(2,[3]),(1,[2])] : Dependencies
**
** In foetus-Programms, these dependecies always appear in the correct order,
** e.g.
**
** ... case a of { C1 b => case b of => { C2 c => ...
*)

structure Deps : DEPENDENCIES = struct

    type Dependency = Ident * Ident list;
    type Dependencies = Dependency list;

    val empty = [] : Dependencies;

    (* findLesses returns a list of variables that are greater than x
     * i.e. returns l  if (x, l) in dep
     *              [] else *)
    fun findLesses(dep,x) =
        case List.find (fn (x', _) => (x' = x)) dep of
            SOME (_, l) => l
          | NONE => [];

    (* addLess adds the dependency x' < x *)
    fun addLess(dep,x',x) = (x', (x::findLesses(dep,x))) :: dep;

    (* addEqual adds the synonym x' = x *)
    fun addEqual(dep,x',x) = raise Error "addEqual in simpledeps not supported";

    (* getRel(dep,y,x) returns rel_less    if y < x
                               rel_equal   if y = x
                               rel_unknown else     *)
    fun getRel(dep,y,x) =
        if (x=y) then rel_equal else
            case List.find (fn (y', _) => (y' = y)) dep of
                SOME (_, l) => if (x mem l) then rel_less
                      else rel_unknown
              | NONE => rel_unknown;

end (* structure Deps *);

(****************************** Call Matrix ******************************
**
** structure for storing the relations between "input parameters" (pars) and
** "output parameters" (args) of a call f->g, e.g.
**
**   f = [x][y][z]...(g a b c d)...
**   where a < x, b < z, c = y, d > z
**
** The call matrix is
**
**      x  y  z
**   a  <  ?  ?
**   b  ?  ?  <
**   c  ?  =  ?
**   d  ?  ?  ?
**
** At any time each row can only contain one "<" or "=", because each arg
** can be dependent of only one par. Therefore you could realize the call
** matrix as a vector like
**
**   a    b    c    d
**   <,x  <,z  =,y  ?
**
** But the advantage of a matrix is that you can use standard matrix
** multiplication based on the ring (? "0", <, = "1") with properly defined
** elementary + and *, when you combine two calls f->g and g->h.
** Be A the call matrix of f->g and B the call matrix of g->h, then
** C = B*A is the call matrix of the combined call f->h.
*)

structure CallMatEl : MATRIX_ELEMENT = struct
    type Element = Relation;

    val null = rel_unknown;
    val one  = rel_equal;
    fun add (rel_less, _) = rel_less
      | add (_, rel_less) = rel_less
      | add (rel_equal, _) = rel_equal
      | add (rel_unknown, rel_equal) = rel_equal
      | add (rel_unknown, rel_unknown) = rel_unknown;
    fun mult (rel_unknown, _) = rel_unknown
      | mult (_, rel_unknown) = rel_unknown
      | mult (rel_less, _) = rel_less
      | mult (rel_equal, rel_less) = rel_less
      | mult (rel_equal, rel_equal) = rel_equal;
end;

structure CallMat = MatrixFUN(CallMatEl);
type CallMatrix = CallMat.Matrix;
open CallMat;

(****************************** Static Environment **********************
**
** The static environment is always present in analyse-functions and stores
** the function headers (FunHead) of the visible foetus functions in the
** current context in a stack (FunStack) and the known dependencies between
** variables (Deps.Dependencies).
*)

type FunHead = ExtIdent * Ident list;
type FunStack = FunHead list;
type StaticEnv = FunStack * Deps.Dependencies;

(****************************** Call graph ******************************
**
** The CallGraph structure stores the vertices (call f -> g with incidental
** call matrix) of the call graph that is built up by "analyse".
** It stores the full names of the callers and the identifiers (Ident) of
** the callees for pretty output reasons (getExtIdent).
*)

type Call = FunHead * Ident * CallMatrix;

signature CALLGRAPH = sig
    type CallGraph;

    val empty:   CallGraph;
    val add:     CallGraph * Call -> CallGraph;
    val addList: CallGraph * Call list -> CallGraph;
    val getExtIdent: CallGraph -> Ident -> ExtIdent;
    val getExtCallers: CallGraph -> ExtIdent list;
    val getCallers: CallGraph -> Ident list;
    val getCalled:  CallGraph * Ident -> Ident list;
    val getCallMats:CallGraph * Ident * Ident -> CallMatrix list;
end;

(* simple list implementation of CALLGRAPH, faster were a tree *)
structure Calls : CALLGRAPH = struct
    type CallGraph = (ExtIdent * Ident * CallMatrix) list;

    val empty = [];
    fun add     (calls, ((f,_), g, m)) = (f,g,m)::calls;
    fun add'    (((f,_), g, m), calls) = (f,g,m)::calls;
    fun addList (calls, callList) = foldl add' calls callList;

    fun getExtIdent ((f as (name,i),_,_)::calls) ident =
        if i=ident then f
        else getExtIdent calls ident
      | getExtIdent [] ident = ("UNKNOWN", ident);

    fun getExtCallers [] = []
      | getExtCallers ((f,_,_)::calls) =
        let val fs = getExtCallers calls in
          if (f mem fs) then fs
          else f::fs
        end;

    fun getCallers [] = []
      | getCallers (((_,f),_,_)::calls) =
        let val fs = getCallers calls in
          if (f mem fs) then fs
          else f::fs
        end;

    fun getCalled ([], _) = []
      | getCalled (((_,f'),g,_)::calls, f) =
        let val gs = getCalled (calls, f) in
            if (not (f=f')) orelse (g mem gs) then gs
            else g::gs
        end;

    fun getCallMats ([], _, _) = []
      | getCallMats (((_,f'),g',m)::calls, f, g) =
        let val ms = getCallMats (calls, f, g) in
            if (f=f') andalso (g=g') then m::ms
            else ms
        end;
end;

(****************************** Analyse ************************************
**
** Master function: analyseDefs
**
** analyseDefs analyses a set of definitions (Defs) in a given environment
** and accumulates a list of calls (Call list). The main task is to transfer
** the tree structure of definition (= term) into a flat list of static
** calls. Therefore you will often see "flatMap" or "@" (append).
**
** Abbreviations:
** se: static environment
** t : term
** x : variable
** i : unique identifier for variable
** v : value
** c : constant
** f : function name
** pars: Parameters [i1, i2, ..., in] of a function
** args: Arguments [t1, t2, ..., tm] of an application (function call)
*)

(* extractFunHead
**
** removes to trailing lambdas of an expression (v), builds the function
** head descriptor and introduces the variables defined by the lambdas
** into the environment
*)

fun extractFunHead pars (fname, v_lam (x,(t,env))) =
      let val i = newGen() in
        extractFunHead (i::pars) (fname, hnf(t,e_gen(x,i)::env))
      end
  | extractFunHead pars (fname,v) = ((fname, rev pars), v)


(* bareFunctionEntry
**
** creates a call from a function to "nothing" out of its head:
**
** to assure that also non-recursive functions appear in the output,
** every defined expression is added to the Call list as "empty call".
** Thus getCallers gets also non-recursive functions.
*)

fun bareFunctionEntry (f, pars) = ((f,[]), emptyIdent, []) : Call;


(* analyseLet'
**
** The option parameter "t_opt" determines whether to analyse the body
** term t that usually appears in
**
**  let defs in t
**
** analyseLet calls analyseLet' with SOME t, analyseDefs with
** NONE, because top level definitions have no "body" to evaluate
** but are treated exactly like a "let" besides.
**
** Five steps of analysing a "let":
**
** 1. create unique identfiers for the defined variables --> extDefs
** 2. insert these into the (common) environment --> extEnv
** 3. build head normal form of the defining terms --> vs
**    extract the function heads --> funs
**    and insert them into the static environment --> fstack'
** 4. analyse the bodies of the defining terms
** 5. possibly analyse the let-body t
**
** Important note:
** to avoid infinite unfolding of definitions, the definitions
** are inserted into the environment not as e_rec but as e_gen to
** prevent further stepping in. This applies to step 4 and 5!
*)

fun analyseLet (se,env,defs,t) = analyseLet' (se,env,defs,SOME t)

and analyseLet' ((fstack,deps,caller),env,defs,t_opt) : Call list =
    let val extDefs = map (fn (x,t) => ((x,newGen()),t)) defs;
        val extEnv = foldl (fn ((xi,t), e) => (e_gen xi)::e) env extDefs;
        val vs = map (fn (xi,t) => (xi,hnf(t,extEnv))) extDefs;
        val funs = map (extractFunHead []) vs;
        val fstack' = (foldl (fn ((fhead,v),l) => fhead::l) fstack funs) in
        (flatMap (fn (caller,v) => (bareFunctionEntry caller) ::
                  (analyseBody (fstack',deps,caller) v))
         funs) @
        (case t_opt of
             SOME t => analyseBody (fstack',deps,caller)
                                   (hnf(t,extEnv))
           | NONE => [])
    end


(* analyseBody
**
** treats simple terms and passes complicated terms to special functions
*)

and analyseBody se (v_c(c,v)) = analyseBody se v
  | analyseBody se (v_c_lazy(c,cl)) = analyseBody se (hnf(cl))
  | analyseBody se (v_tup(cvs)) =
      flatMap (fn (c,v) => analyseBody se v) cvs
  | analyseBody se (v_tup_lazy(cts,env)) =
      flatMap (fn (c,t) => analyseBody se (hnf(t,env))) cts
  | analyseBody se (v_dot(v,c)) = analyseBody se v
  | analyseBody se (v_app(v,cl)) = analyseApp (se, v, [cl])
  | analyseBody se (v_case(v,pats,env)) = analyseCases(se, v, pats, env)
  | analyseBody se (v_gen(x,i)) = analyseCall(se, i, []) (* no args *)
  | analyseBody se (v_let (defs,t,env)) = analyseLet (se,env,defs,t)
  | analyseBody se (v_def (cl)) = []
  | analyseBody se (v_lam(x,(t,env))) = analyseBody se (hnf(t,addGen(x,env)))
(*
** discard lambda: see example ord.fts
** can treat e.g.  add = [x][y]case x of { ... Lim f => Lim([z]add (f z) y) };

      raise Error "analyse: don't know how to treat lambda"
*)


(* analyseCase(s|NoDep)
**
** analyseCases performs the analyzation of all branches by passing them
** eather to analyseCase or to analyseCaseNoDep:
**
** If the regarded term v evaluates to a variable x (v_gen) then analyseCase
** is called for each case. analyseCase adds the a "less x" relation for the
** newly defined variable x' in the regarded case before analysing the body
** by the specified analyseFun (that is usually analyseBody, but can be
** e.g. analyseApp as well).
**
** Otherwise (if v not variable) foetus can not determine, whether the
** newly defined variables are less or equal to v; thus no relations are
** added into deps. But here v has to be analysed itself.
*)

and analyseCases' analyseFun (se, v_gen(x,i), pats, env) =
      flatMap (analyseCase' analyseFun se env i) pats
  | analyseCases' analyseFun (se, v, pats, env) =
      flatMap' (analyseBody se v) (analyseCaseNoDep' analyseFun se env) pats

and analyseCase' analyseFun (fstack,deps,caller) env i (c, (x', t)) =
    let val i' = newGen() in
        analyseFun (fstack,Deps.addLess(deps,i',i),caller)
                    (hnf(t,e_gen(x',i')::env))
    end

and analyseCaseNoDep' analyseFun se env (c, (x', t)) =
      analyseFun se (hnf(t,addGen(x',env)))

and analyseCases svpe = analyseCases' analyseBody svpe

(* analyseApp
**
** analyseApp gathers nested applications (because functions with more
** than one parameter are curried) and forms one call.
** e.g. (((f a) b) c) --> f(a,b,c)
**
** special cases:
** 1. f is a case-term: ((case x of {... | C_i x' => t_i | ...}) y) :
**    the whole case-term is analysed and each branch term is considered
**    a function to be applied
** 2.
**
** 4. f is a lambda term: a beta-reduction is performed (([x] t) y) --> t[x:=y]
*)

and analyseApp (se, v_app(v,cl), args) =
      analyseApp (se, v, cl::args)
  | analyseApp (se, v_gen(x,i), args) = analyseCall (se, i, args)
  | analyseApp (se, v_def(cl), args) =
      flatMap (analyseBody se) (map hnf args)
      (* don't step into defined functions, register Call but analyse args *)
  | analyseApp (se, v_case(v,pats,env), args) =
      analyseCases' (fn se' => (fn v' => (* (analyseBody se' v') @ *)
                                         (analyseApp(se', v', args))))
      (se,v,pats,env)
  | analyseApp (se, v_lam(x, (t, env)), cl::args) =
      analyseApp (se, hnf(t,e_val(x,cl)::env), args)
(*
  | analyseApp (se, v, []) = analyseBody se v
      (*raise Error "analyseApp: app without args*)
*)
  | analyseApp _ = raise Error
       "analyseApp: application of 'let', 'tup' and 'dot' not supported"


(* analyseCall
**
** analyseCall is called by analyseApp to further process a call from "caller"
** (f) to "g" with the values of "args" as arguments. It puts the args in
** head normal form (vs), passes each of them to further analyzation to
** analyseBody (because they can contain calls themselves) and produces
** a call f->g with belonging call matrix that is added to the call graph.
*)

and analyseCall (se as (fstack,deps,caller as ((f,i),pars)), g, args) =
    let val vs = map hnf args in (
        if (!debug) then
          print ("analysing call in "^f^(identToString i)^"("^
            (printList "," (map identToString pars))^"): "^
            (identToString g)^"("^
            (printList "," (map printValue vs))^")\n")
        else ();
        flatMap' [(caller, g, buildCallMat (pars, deps, vs))]
                 (analyseBody se) vs
        )
    end

and buildCallMat (pars, deps, []) = []
  | buildCallMat (pars, deps, v::vs) = (map (getRelation deps v) pars) ::
      buildCallMat (pars, deps, vs)

(* getRelation
**
** compares value v with variable par using the stored deps and returns
** rel_less, rel_equal or rel_unknown.
**
** Considered cases:
** 1. x = C y   => y < x  (C constructor)
** 2. x R v.L   <= x R v  (L label, R in <, =, ?)
** 3. x R (v a) <= x R v  (a argument(s))
**
** Not-yet considered cases:
** 1. tupels
** 2. further evaluation of v
*)

and getRelation deps (v_gen(x,i)) par = Deps.getRel(deps,i,par)
  | getRelation deps (v_dot(v,c)) par = (
    (* print ("getRelation v_dot, v="^(printValue v)^"\n"); *)
      getRelation deps v par)
  | getRelation deps (v_app(v,cl)) par = getRelation deps v par
(*
** discard parameter of application; see example ord.fts
** thus e.g. (f z) < Lim f
*)
  | getRelation deps (v_def(cl)) par = rel_unknown
  | getRelation deps v par = rel_unknown;


fun analyseDefs (se,env,defs) = analyseLet' (se,env,defs,NONE)


val emptyStaticEnv = ([],            (* empty Function stack *)
                      Deps.empty,    (* no Dependencies *)
                      (emptyExtIdent,[]));   (* non-existent caller "TOP" *)

