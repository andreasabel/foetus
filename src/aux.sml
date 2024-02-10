(*
** aux.sml
**
** by Andreas Abel, Thorsten Altenkirch
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** auxiliary functions
*)
 
(* Compiler.Control.Print.printLength := 1000; *)
(* Compiler.Control.Print.printDepth := 350; *)
(* Compiler.Control.Print.stringDepth := 250; *)

fun variant x ys =
      let fun var x [] = x
            | var x (y::ys') =
                 if x=y then var (x^"'") ys
                 else var x ys'
      in var x ys
      end;

exception Assoc;

fun assoc(c,[]) = raise Assoc
  | assoc(c,(c',x)::p) = if c=c' then x else assoc(c,p);


fun removeFirst f [] = NONE
  | removeFirst f (y::ys) =
      if f y then SOME (y,ys)
      else (case removeFirst f ys of
                (SOME (x,ys')) => SOME (x,y::ys')
              | NONE => NONE);

infix mem;
fun el mem list = List.exists (fn el' => (el'=el)) list;

fun union set [] = set
  | union set (el::list) =
    if (el mem set) then union set list
    else union (el::set) list;

(* simple version of union sufficent because = checks content, not pointer
**
fun union eqFn set [] = set
  | union eqFn set (el::list) =
    if (List.exists (eqFn el) set) then union eqFn set list
    else union eqFn (el::set) list;
*)

fun flatMap' resultList f list =
    List.foldl (fn (el, resultList') => f(el) @ resultList') resultList list;

fun flatMap f l = flatMap' [] f l;

fun dropNth 0 (el::list) = list
  | dropNth n (el::list) = el :: (dropNth (n-1) list)
  | dropNth _ [] = [];

fun extractNth 0 (el::list) = (el, list)
  | extractNth _ [] = raise Subscript
  | extractNth n (el::list) =
    let val (nth, remList) = extractNth (n-1) list
    in (nth, el::remList)
    end;

fun upto(l,u) = if (l >= u) then [] else l :: upto (l+1, u);
