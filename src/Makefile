files = \
  aux.sml \
  closure.sml \
  foetus.sml \
  matrix.sml \
  analyse.sml \
  check.sml \
  parser-hooks.sml \
  foetus.grm.sig \
  foetus.grm.sml \
  foetus.lex.sml \
  parser-main.sml \
  top.sml \
  main.sml

all : ../bin ../bin/foetus

../bin/foetus : foetus.mlb $(files)
	mlton -output $@ $<

foetus.lex.sml : foetus.lex
	ml-lex $<

foetus.grm.sig foetus.grm.sml : foetus.grm
	ml-yacc $<

../bin :
	mkdir $@
