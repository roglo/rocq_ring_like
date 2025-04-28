TARGET=RingLike.vo RealLike.vo IterMul.vo IterAnd.vo IterMax.vo DerivMul.vo NatRingLike.vo
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

.SUFFIXES: .v .vo

%.vo: %.v
	$(ROCQ) $(ROCQ_OPT) -R . RingLike $<

.PHONY: all clean depend

include .depend
