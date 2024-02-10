# Build foetus

.PHONY: test
test : bin/foetus
	bin/foetus examples/nat.fts
	bin/foetus examples/ord.fts
	bin/foetus examples/lists.fts
	bin/foetus examples/fintree.fts
	bin/foetus examples/max3.fts
	bin/foetus examples/gegenbsp.fts
	bin/foetus examples/testcheck.fts

bin/foetus :
	make -C src
