all:

clean:
	-make -f Makefile.coq cleanall
	-rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

_CoqProject:
	:

%: Makefile.coq
	make -f Makefile.coq $@
