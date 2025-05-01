# Default target
all: RocqMakefile
	+@$(MAKE) -f RocqMakefile all
.PHONY: all

# Permit local customization
-include Makefile.local

# Forward most targets to Rocq makefile (with some trick to make this phony)
%: RocqMakefile phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f RocqMakefile $@
phony: ;
.PHONY: phony

clean: RocqMakefile
	+@$(MAKE) -f RocqMakefile clean
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	find . -maxdepth 1 \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f RocqMakefile* .lia.cache builddep/*
.PHONY: clean

# Create Rocq Makefile.
RocqMakefile: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o RocqMakefile $(EXTRA_COQFILES)

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) -y $(BUILDDEPFILES)
.PHONY: builddep

# Some files that do *not* need to be forwarded to RocqMakefile.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local _CoqProject $(OPAMFILES):: ;
