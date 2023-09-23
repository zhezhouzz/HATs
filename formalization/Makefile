.DEFAULT_GOAL := all

COQMAKEFILE := Makefile.coq

COQPROJECT ?= _CoqProject

-include $(COQDOCMAKEFILE)

%: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@

clean: cleanall
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf
.PHONY: clean

$(COQMAKEFILE): $(COQPROJECT) FORCE
	@coq_makefile -f $(COQPROJECT) -o $@

FORCE Makefile $(COQDOCMAKEFILE) _CoqProject: ;
