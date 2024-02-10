
val version = "foetus $Revision: 1.0 $";

structure FoetusLrVals = FoetusLrValsFun(structure Token = LrParser.Token);
structure FoetusLex = LexFun(structure Tokens = FoetusLrVals.Tokens);
structure FoetusParser = Join(structure LrParser = LrParser
                             structure ParserData = FoetusLrVals.ParserData
                             structure Lex = FoetusLex);

open TextIO; (* inputLine, output, stdErr *)

fun lexer s = FoetusParser.makeLexer (fn _ => 
  case TextIO.inputLine s
   of NONE => ""
    | SOME x => x);

val EOF = FoetusLrVals.Tokens.EOF(0,0);

exception Parser of string*int;

(* rather use stdOut instead of stdErr, because of CGI *)
val errOut = TextIO.stdOut;

fun parseStream b s =
      let fun loop lexer =
                (if b then print "foetus: " else ();
                 let val (_,lexer) =
                      FoetusParser.parse(0,lexer,
                                        fn (s,l,_) =>
                                        raise Parser (s,l),());
                     val (next,lexer) = FoetusParser.Stream.get lexer
                 in if FoetusParser.sameToken(next,EOF)
                    then ()
                    else loop lexer
                end)
                handle Parser (s,i) =>
                    (output (errOut,"Parser Error - line "^(Int.toString i)^
                                     ": "^s^"\n"); start ())
(*                   | Interrupt =>
                           (output (errOut,"User interrupted!\n"); start())
*)                   | _ =>
                           (output (errOut,"Parser Error ???\n");start ())
(*                   | LexError  =>
                           (output (errOut,"Lex Error ???\n");start ())
*)        and start () = loop (lexer s)
      in start ()
      end;
