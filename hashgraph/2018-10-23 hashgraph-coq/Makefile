
COQC = coqc
COQDEP = coqdep

UNITS = \
	Calculate \
	Cardinality \
	Consensus \
	Decide \
	Decision \
	Fairness \
	Famous \
	Hashgraph \
	HashgraphFacts \
	Majority \
	Median \
	Order \
	Progress \
	Received \
	Relation \
	Round \
	Sees \
	Tact \
	Timestamp \
	Vote \
	Weight

SOURCES = $(foreach i, $(UNITS), $(i).v)
OBJS = $(foreach i, $(UNITS), $(i).vo)

.PHONY : all clean

all : $(OBJS)

%.vo : %.v
	$(COQC) -q $<

clean :
	rm *.vo *.glob

depend : $(SOURCES) Makefile
	$(COQDEP) $(SOURCES) > depend

tags : $(SOURCES)
	coqtags $(SOURCES)

include depend
