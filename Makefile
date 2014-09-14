.PHONY: all
all: compiler.byte

MODULES   = arch reg proc debuginfo mach cmm selectgen selection printcmm printmach printlinear \
	printclambda liveness linearize emitaux \
	CSEgen CSE liveness interf reloadgen reload spill coloring split \
	deadcode clambda compilenv comballoc strmatch cmmgen cmm closure \
	js asmgen optcompile main


BYTE_OBJS = $(addsuffix .cmo,$(MODULES))
SRCS = $(addsuffix .ml, $(MODULES))

%.cmo: %.ml
	ocamlc -I +compiler-libs -annot -c -g $<

%.cmi: %.mli
	ocamlc -I +compiler-libs -c $<

compiler.byte: $(BYTE_OBJS)
	ocamlc -o $@ -g -I +compiler-libs ocamlcommon.cma $^

.PHONY: clean
clean:
	rm -f *.cm[iot] *.cmti compiler.byte

.PHONY: depend
depend:
	ocamldep -I +compiler-libs *.ml > .depend

-include .depend
