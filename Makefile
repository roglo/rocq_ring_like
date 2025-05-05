TARGET=RingLike.vo RealLike.vo IterMul.vo IterAnd.vo IterMax.vo DerivMul.vo NatRingLike.vo ZRingLike.vo LapRingLike.vo PolynomialRingLike.vo
FILESFORDEP=`LC_ALL=C ls *.v`
ROCQ=rocq compile
ROCQ_OPT=

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	rocq dep $(FILESFORDEP) | sed -e " s|$$HOME[^ ]*||" | \
	LC_ALL=C sort |	sed -e 's/  *$$//' > .depend

install:
	@echo "Installing RingLike..."
	@mkdir -p $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib
	@cp -r . $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RingLike

uninstall:
	@echo "Uninstalling RingLike..."
	@rm -rf $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RingLike

local_opam_pin_add:
	opam pin add rocq-ring-like . -n -y
	opam reinstall rocq-ring-like -y -w

.SUFFIXES: .v .vo

%.vo: %.v
	$(ROCQ) $(ROCQ_OPT) -R . RingLike $<

.PHONY: all clean depend install uninstall local_opam_pin_add

include .depend
