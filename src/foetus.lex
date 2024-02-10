(*
** foetus.lex
**
** by Andreas Abel, Thorsten Altenkirch
** Copyright 1998 Ludwigs-Maximilians-Universit"at M"unchen
**
** tokens for foetus language; input for ml-lex
*)


structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b)token = ('a,'b) Tokens.token
type lexresult= (svalue,pos)token

open Tokens

val pos = ref 0
val eof = fn () => EOF(!pos,!pos)

%%
%header (functor LexFun(structure Tokens: Foetus_TOKENS) : LEXER);
%s COM;
small=[a-z];
cap=[0-9A-Z];
alpha=[A-Za-z];
digit=[0-9];
name=({alpha}|{digit}|_|')*;
space=[\t\ ];
%%
<INITIAL>{space}    => (lex());
<INITIAL>\n         => (pos:=(!pos)+1;lex ());
<INITIAL>"["        => (LBRA(!pos,!pos));
<INITIAL>"]"        => (RBRA(!pos,!pos));
<INITIAL>"("        => (LPAR(!pos,!pos));
<INITIAL>")"        => (RPAR(!pos,!pos));
<INITIAL>"{"        => (LCUR(!pos,!pos));
<INITIAL>"}"        => (RCUR(!pos,!pos));
<INITIAL>"|"        => (BAR(!pos,!pos));
<INITIAL>","        => (COMMA(!pos,!pos));
<INITIAL>"."        => (DOT(!pos,!pos));
<INITIAL>"="        => (EQUALS(!pos,!pos));
<INITIAL>":"        => (COLON(!pos,!pos));
<INITIAL>";"        => (SEMICOLON(!pos,!pos));
<INITIAL>"=>"       => (DARR(!pos,!pos));
<INITIAL>"->"       => (TO(!pos,!pos));
<INITIAL>"let"      => (LET(!pos,!pos));
<INITIAL>"in"       => (IN(!pos,!pos));
<INITIAL>"case"     => (CASE(!pos,!pos));
<INITIAL>"of"       => (OF(!pos,!pos));
<INITIAL>"Set"      => (SET(!pos,!pos));
<INITIAL>"Type"     => (TYPE(!pos,!pos));
<INITIAL>"#nf"      => (C_NF(!pos,!pos));
<INITIAL>"#nf'"      => (C_NF'(!pos,!pos));
<INITIAL>"#hnf"      => (C_HNF(!pos,!pos));
<INITIAL>"#hnf'"      => (C_HNF'(!pos,!pos));
<INITIAL>"#eq"      => (C_EQ(!pos,!pos));
<INITIAL>"#eq'"      => (C_EQ'(!pos,!pos));
<INITIAL>"#cxt"      => (C_CXT(!pos,!pos));
<INITIAL>"#env"      => (C_ENV(!pos,!pos));
<INITIAL>"#include"    => (C_INCLUDE(!pos,!pos));
<INITIAL>{small}{name} => (ID (yytext,!pos,!pos));
<INITIAL>{cap}{name}   => (CONST (yytext,!pos,!pos));
<INITIAL>"(*"        => (YYBEGIN COM; lex());
<INITIAL>"\""[^\"\n]*"\"" => 
      (STRING (substring(yytext,1,(size yytext)-2),!pos,!pos));
<COM>\n       	=> (pos:=(!pos)+1;lex ());
<COM>[^()*\n]+	=> (lex());
<COM>"(*"	=> (lex());
<COM>"*)"	=> (YYBEGIN INITIAL; lex());
<COM>[*()]	=> (lex());
