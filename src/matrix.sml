(*
** matrix.sml
**
** by Andreas Abel
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** polymorphic matrices
**
*)

signature MATRIX_ELEMENT = sig
    type Element;

    val null: Element;
    val one : Element;
    val add : Element * Element -> Element;
    val mult: Element * Element -> Element;
end;
(* use "aux.sml" *)

signature MATRIX = sig
    type Row;
    type Matrix;

    val transpose: Matrix -> Matrix;
    val mult     : Matrix * Matrix -> Matrix;
    val diag     : Matrix -> Row;
end;

functor MatrixFUN(El: MATRIX_ELEMENT) : MATRIX = struct
    type Row = El.Element list;
    type Matrix = Row list;

    open List;

    fun transpose [] = []
      | transpose ([]::_) = []
      | transpose rows = (map hd rows) :: (transpose (map tl rows));
    fun mult' ([],_) = []
      | mult' (rows, cols) = map (fn row => map (fn col =>
          foldl El.add El.null (ListPair.map El.mult (row,col))) cols) rows;
    fun mult (a,b) = mult' (a,(transpose b));
    fun diag ((el::row)::rows) = el :: (diag (map tl rows))
      | diag _ = [];
    fun delRow (rows, n) = dropNth n rows;
    fun delCol (rows, n) = map (dropNth n) rows;

end;
