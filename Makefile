# -*- Makefile -*-

# --------------------------------------------------------------------
INCFLAGS := -I .
SUBDIRS  :=
COQFILES := krivine.v
COQDOCJS := coqdocjs

COQDOCFLAGS := \
  --toc --toc-depth 2 --html --interpolate \
	--external 'http://math-comp.github.io/math-comp/htmldoc/' mathcomp \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(COQDOCJS)/extra/header.html \
	--with-footer $(COQDOCJS)/extra/footer.html
export COQDOCFLAGS

-include Makefile.common

# --------------------------------------------------------------------
this-clean::
	rm -f *.glob *.d *.vo

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: html

html: config build
	rm -rf html && $(COQMAKE) html
	cp $(COQDOCJS)/extra/resources/* html

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = krivine
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
     awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
