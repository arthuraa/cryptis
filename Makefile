# Default target
all: Makefile.rocq
	+@$(MAKE) -f Makefile.rocq all
.PHONY: all

# Build with dune.
# This exists only for CI; you should just call `dune build` directly instead.
dune:
	@dune build --display=short
.PHONY: dune

# Permit local customization
-include Makefile.local

# Generate the _RocqProject file.
_RocqProject: gen_RocqProject.sh config/paths config/flags config/source-list $(wildcard config/local)
	@./$< > $@

# Forward most targets to Rocq makefile (with some trick to make this phony)
%: Makefile.rocq phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.rocq $@
phony: ;
.PHONY: phony

clean: Makefile.rocq
	+@$(MAKE) -f Makefile.rocq clean
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -rf Makefile.rocq Makefile.rocq.conf .lia.cache builddep/* _build */_RocqProject
	# We do not clean _RocqProject since ProofGeneral and other editors need that,
	# and 'make clean' is often needed to remove the .vo files after a dependency update.
.PHONY: clean

# Create Rocq Makefile.
Makefile.rocq: _RocqProject Makefile
	"$(COQBIN)rocq" makefile -f _RocqProject -o Makefile.rocq $(EXTRA_COQFILES)

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

# Backwards compatibility target
build-dep: builddep
.PHONY: build-dep

# Some files that do *not* need to be forwarded to Makefile.rocq.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local config/paths config/flags config/source-list config/local $(OPAMFILES):: ;
