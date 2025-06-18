MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
	       \) -print						|	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined|jww)'	|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: category-theory

category-theory: Makefile.coq $(wildcard *.v)
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

todo:
	-@$(MISSING) || exit 0

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

PARALLEL = parallel
COQ_TOOLS = $(HOME)/src/coq-tools

minimize-requires:
	@if [ ! -f $(COQ_TOOLS)/minimize-requires.py ]; then \
	    echo "Need https://github.com/JasonGross/coq-tools"; \
	fi
	@$(PARALLEL) -j1 --progress -- \
	    $(COQ_TOOLS)/minimize-requires.py -i -R . Category {} ::: \
	    $$(find . -name '*.v')

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force
