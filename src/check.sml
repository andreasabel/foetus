(*
** check.sml
**
** by Andreas Abel
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** the BRAIN of foetus: call graph completion and finding a lexical order
**
*)


(****************************** call graph completion *********************)

open Calls;

(* compose' g->h * (h->f)s *)
fun compose' hs g = map (fn h => CallMat.mult(h,g)) hs;

fun compose hs gs = flatMap (compose' hs) gs;

(* circle
**
** finds connections from g to f avoiding visited
fun circle calls f =
    let val out = ref (identToString g)
        and outList = ref [] in
    let fun extendId i = extIdentToString (getExtIdent calls i)
        and circle' visited g out =
        if (g mem visited) then [] else
        flatMap (fn (h) => if (h=f) then (outList := out::(!outList);
                                          getCallMats(calls,g,h))
                           else compose (circle' (g::visited) h
                                              (out^" -> "^(extendId h)))
                                         (getCallMats(calls,g,h)))
                (getCalled (calls,g))
    in let val result = circle' [] f (extendId g) in
        if !verbose then let
            fun printPath(out,relMat) =
                print ((printList " " (map printRel (diag relMat)))^": "^
                       (out)^" -> "^(extendId f)^"\n")
        in ListPair.app printPath (!outList, result)
        end else ();
        result
    end end end;
*)

(*
** Call Graph Completion
**
** analyse extracts direct calls between funtions and stores them in a
** call graph. This graph is a directed multigraph, multiple edges from
** one vertex to another are allowed if their tags differ. Each edge is
** tagged with a call matrix.
**
** completion finds all different indirect calls and add them to the call
** graph. This is how 'complete' works:
** We start with the 'basic' graph built by analyse as working graph.
** In each step we combine for all vertices f, g, h every edge f->g
** in our working graph with every edge g->h in the basic graph.
** The call matrix of a 'composed call' f->h is the matrix product of
** tag(g->h) and tag(f->g)
*)

(* verbose variant of completion algorithm (V)
**
** each edge in the call graph is added a visited nodes list
** each visited list contains the callee node in the beginning
*)


(* g->h * (h->f)s *)
fun composeCallsV' h_fs (g_h as (caller1, callee1, callMat1), visited1) =
    foldl (fn ((((_,caller2), callee2, callMat2), visited2), doneList) =>
            if (caller2 = callee1) then ((caller1, callee2,
                CallMat.mult(callMat2,callMat1)), visited1 @ visited2)
                ::doneList
            else doneList)
          [] h_fs;

fun composeCallsV h_fs g_hs = flatMap (composeCallsV' h_fs) g_hs;

fun unionV set [] = set
  | unionV set ((el,v)::list) =
    if List.exists (fn (el',_) => (el'=el)) set then unionV set list
    else unionV ((el,v)::set) list;

fun completeV'(total,basic) =
    let val totalNew = unionV total (composeCallsV total basic) in
        if (length totalNew) = length total then totalNew
        else completeV'(totalNew,basic)
    end;

fun completeV calls = completeV'(calls,calls);

fun completeV calls =
    let fun completeV' total =
        let val totalNew = unionV total (composeCallsV total calls) in
            if (length totalNew) = length total then totalNew
            else completeV' totalNew
        end
    in completeV' calls end;

fun createVisitedList (call as (_,callee,_)) = (call, [callee]);

fun circleV calls f =
    let fun extendId i = extIdentToString (getExtIdent calls i)
        and printVCall ((caller,callee,relMat),visited) =
            print ((printList " " (map printRel (diag relMat)))^": "^
                (extIdentToString caller)^" -> "^
                (printList " -> " (map extendId visited))^"\n")
    in
        foldl (fn (call as (((_,caller),callee,callMat),visited), doneList) =>
            if (f=caller) andalso (caller=callee) then (
                printVCall call;
                callMat::doneList)
            else doneList)
          [] (completeV (map createVisitedList calls))
    end;

(*
** saturation (completion) algorithm
*)

fun composeCalls' h_fs (g_h as (caller1, callee1, callMat1)) =
    foldl (fn (((_,caller2), callee2, callMat2), doneList) =>
            if (caller2 = callee1) then (caller1, callee2,
                CallMat.mult(callMat2,callMat1))::doneList
            else doneList)
          [] h_fs;

fun composeCalls h_fs g_hs = flatMap (composeCalls' h_fs) g_hs;

fun complete calls =
    let fun complete' total =
        let val totalNew = union total (composeCalls total calls) in
            if (length totalNew) = length total then totalNew
            else complete' totalNew
        end
    in complete' calls end;

fun circle calls f =
    if !verbose then circleV calls f
    else foldl (fn (((_,caller),callee,callMat), doneList) =>
      if (f=caller) andalso (caller=callee) then callMat::doneList
      else doneList)
    [] (complete calls);

(****************************** lexical order ******************************)

exception NoOrder;

(*
** About the lexicalOrder-algorithm:
** ---------------------------------
**
** Variable relMat/argRels: Relation list list
**
** Each column of this matrix represents one recursive call f->f.
** The column elements represent the relations of the function paramaters to
** the call arguments (this is the main diagonal of the call matrix).
** E.g. f[x,y,z] -> f(a,b,c) {x<a, y=b}: row: < = ?
** Thus each row represents one variable and the row elements the relations
** in the different calls. A permutation of the rows fits a permutation of
** the parameters of a function.
**
** Idea:
**
** To find a lexical order in relMat you delete one row (rels) that contains
** at least one less(<)- and no unknown(?)-relations from relMat.
** Each column of this vector (rels) that is a < is removed from relMat.
** (elimCols)
** You repeat these steps until the matrix vanished.
** (findOrder)
** If there is no permutation of the rows, so that the matrix vanishes if you
** eliminate the rows in the way described above, then no lexical order exists.
** (exception NoOrder).
*)

(*
** elimCols(rels:      Relation list,
**          colNo:     int,
**          relMat:    Relation list list,
**          foundLess: boolean): Relation list list
**
** works off rels and deletes the corresponding column in relMat whenever
** '<' (rel_less) appears. If a '?' (rel_unknown) appears 'NoOrder' is raised
** to indicate to findOrder that the current permutation of the parameters
** represents no lexical order.
** foundLess indicates whether rels contained a '<' so far (must be 'false' in
**   the initial call).
** colNo specifies the current column of rels/relMat that is considered (must
**   be 0 in the initial call).
*)

fun elimCols ([], _, relMat', foundLess) =
      if foundLess then relMat' else raise NoOrder
  | elimCols (rel_unknown::_, _, _, _) = raise NoOrder
  | elimCols (rel_less::rels, colNo, relMat', _) =
      elimCols (rels, colNo, (map (dropNth colNo) relMat'), true)
  | elimCols (rel_equal::rels, colNo, relMat', foundLess) =
      elimCols (rels, colNo+1, relMat', foundLess);


(*
** findOrder(rowIndex: int,
**           relMat:   Relation list list,
**           argNames: 'a list): 'a list;
**
** tries to find a lexical order on relMat starting with parameter no.
** rowIndex. If elimCols succeds it steps further to look the next parameter,
** otherwise it tries the next parameter (handle NoOrder). If no more
** parameter is left to try (handle Subscript), back-tracking is performed
** (raise NoOrder).
** All permutations of the parameters/rows are considered one after the other
** and the first successfull is returned.
**
** argNames is a list of the names of the parameters (e.g. 0, 1, 2, ...).
*)

fun findOrder (_, [], _) = []
  | findOrder (_, []::_, _) = []
  | findOrder (rowIndex, relMat, argNames) =
    let val rels  = List.nth (relMat, rowIndex)    (* raises Subscript *)
        and rowNo = List.nth (argNames, rowIndex)
    in rowNo :: findOrder (0, elimCols (rels, 0, (dropNth rowIndex relMat),
                                        false),
                           (dropNth rowIndex argNames))
        handle NoOrder => findOrder (rowIndex+1, relMat, argNames)
    end handle Subscript => raise NoOrder;


(*
** lexicalOrder(argRels: Relation list list): int list option
**
** tries to find a lexical order in argRels by calling findOrder,
** giving it the numbers 0, 1, 2, ... as parameter names.
*)

fun lexicalOrder' [] = SOME []
  | lexicalOrder' argRels =
      (SOME (findOrder (0, argRels, upto(0, length argRels))))
      handle NoOrder => NONE;

fun lexicalOrder ([]::_) = NONE   (* recursive function of arity 0 *)
  | lexicalOrder recCalls = lexicalOrder' (transpose recCalls);


(*
** for debugging:
**

fun term calls f =
    let val relMat = (map diag (circle calls f)) in
        (relMat, lexicalOrder relMat)
    end;

fun termination calls = (calls, map (term calls) (getCallers calls));

fun termDefs (se, env, defs) =
      termination (complete (union [] (Calls.addList (Calls.empty, analyseDefs (se, env, defs)))));

fun checkDefs (env, defs) = termDefs (emptyStaticEnv, env, defs);
*)

fun checkDefs (env, defs) =
    let val calls = (union [] (Calls.addList (Calls.empty,
        analyseDefs (emptyStaticEnv, env, defs)))) in
    let fun term f = lexicalOrder (map diag (circle calls f))
        (* completion is done for each function f for verbosity reasons *)
    in
        foldl (fn ((name,f), variants) =>
              let val nameVar = variant name variants in
                  (case term f of
                       NONE => print (nameVar^" FAILS termination check\n")
                     | SOME order => print (nameVar^" passes termination check"^
                            (if (!verbose) andalso not (null order) then
                                 (" by lexical order "^
                                  (printList " " (map Int.toString order))^"\n")
                             else "\n"));
                   (nameVar::variants))
              end)
        [] (rev (getExtCallers calls))
    end end;

(*
** for debugging
**
fun analyseLastDefs ((e_rec defs)::env) =
      analyseDefs (emptyStaticEnv, env, defs);

analyseLastDefs (!globalEnv);

fun testcircle callList f =
      circle (Calls.addList (Calls.empty, callList)) f [] f;

fun termLastDefs ((e_rec defs)::env) =
      termDefs (emptyStaticEnv, env, defs);

termLastDefs (!globalEnv)
handle Error s => (print ("Error :"^s); raise Error s);


val defs = ((fn ((e_rec def)::env) => def) (!globalEnv));
val env = [];
val calls = Calls.addList (Calls.empty,
        analyseDefs (emptyStaticEnv, env, defs));
val f = hd (getCallers calls);
val calls = (union [] calls);
val recCalls = (map diag (circleV calls f));
lexicalOrder recCalls;

**
*)

