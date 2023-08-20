CC     = gcc
RACKET = racket
RM     = rm

lambda:
	./compiler-Llambda.rkt

dyn:
	./compiler-Ldyn.rkt

gradual:
	./compiler-gradual.rkt

poly:
	./compiler-poly.rkt

runtime.o: runtime.c runtime.h
	$(CC) -c -g -std=c99 runtime.c

test: runtime.o
	$(RACKET) run-tests.rkt

clean:
	$(RM) -f *.o *.out *.exe *.s *~
