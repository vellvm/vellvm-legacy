# NOTE:  This Makefile  is setup  to be  used as  the Makefile  for each
# example  development.   It  makes  no  sense as  a  Makefile  for  the
# top-level `examples` directory.

############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
#  Other targets:
#    rebuild       - regenerates files from Ott language specifications
#
############################################################################

include ../Makefile.config

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

## Include directories, one per line.

INCDIRS = \
	. \
	$(METALIB) \

## Directory where generated HTML documentation should go.

DOCDIR = html

## List of files to be compiled and documented.

FILES = $(patsubst %.v,%,$(wildcard *.v))

## Lists calculated from the above.

VFILES  = $(foreach i, $(FILES), $(i).v)
VOFILES  = lang_def.vo lang_inf.vo $(foreach i, $(FILES), $(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation rebuild
.SUFFIXES: .v .vo

all: ott coq

coq: $(VOFILES)

ott: lang.ott
	$(OTT) -coq lang_def.v lang.ott
	$(LNGEN) --coq-admitted --coq-ott lang_def --coq lang_inf.v lang.ott

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -g --quiet --noindex --html -d $(DOCDIR) $(VFILES)
	cp -f ../custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o lang_def.v lang_inf.v
	rm -rf $(DOCDIR)

############################################################################

%.vo: %.v
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES)
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend

############################################################################

OTT_SOURCE = $(patsubst %.ott,%,$(wildcard *.ott))

rebuild:
	$(OTT) -coq $(OTT_SOURCE)_def.v $(OTT_SOURCE).ott
	$(LNGEN) --coq $(OTT_SOURCE)_inf.v --coq-ott $(OTT_SOURCE)_def --coq-loadpath metatheory  $(OTT_SOURCE).ott

