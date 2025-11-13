CATEGORYTHEORY := $(shell find ./coq-cat/ -not -path "./coq-cat/deprecated/*" -not -path "./coq-cat/_opam/*" -not -path "./coq-cat/.local/*" -iname '*.v')
MACLANES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -not -path "./.local/*" -not -path "./coq-cat/*" -iname '*.v')

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

all: Makefile.coq $(CATEGORYTHEORY) $(MACLANES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(CATEGORYTHEORY))
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(MACLANES))
all-quick: Makefile.coq $(CATEGORYTHEORY) $(MACLANES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(CATEGORYTHEORY))
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(MACLANES))
.PHONY: all all-quick

cat: Makefile.coq $(CATEGORYTHEORY)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(CATEGORYTHEORY))
cat-quick: Makefile.coq $(CATEGORYTHEORY)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(CATEGORYTHEORY))
.PHONY: cat cat-quick

maclane: Makefile.coq $(MACLANES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(MACLANES))
maclane-quick: Makefile.coq $(MACLANES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(MACLANES))
.PHONY: maclane maclane-quick

Makefile.coq: Makefile $(MACLANES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -deprecated-from-Coq"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-arg -w -arg -stdlib-vector"; \
	 echo "-arg -w -arg -parsing"; \
	 echo "-arg -w -arg -intuition-auto-with-star"; \
	 echo "-R coq-cat/imports Category"; \
	 echo "-R coq-cat/Lib Category.Lib"; \
	 echo "-R coq-cat/Theory Category.Theory"; \
	 echo "-R coq-cat/Instance Category.Instance"; \
	 echo "-R coq-cat/Construction Category.Construction"; \
	 echo "-R Ch_I Ex.Ch_I"; \
	 echo $(CATEGORYTHEORY); \
	 echo $(MACLANES)) > _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
.PHONY: Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean || true
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -delete || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf .lia.cache .nia.cache
.PHONY: clean