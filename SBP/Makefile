CPSAFLAGS = +RTS -M2048m -N -RTS

SRCS := $(wildcard *.scm) $(wildcard *.prot) $(wildcard *.lsp)

include cpsa4.mk

all:	$(SRCS:%.scm=%_shapes.xhtml) $(SRCS:%.scm=%.xhtml) \
	$(SRCS:%.prot=%_shapes.xhtml) $(SRCS:%.prot=%.xhtml) \
	$(SRCS:%.lsp=%_shapes.xhtml) $(SRCS:%.lsp=%.xhtml)

clean:
	-rm *.txt *.xhtml
