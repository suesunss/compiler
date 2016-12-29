OBJ=tp_y.o tp_l.o tp.o print.o dummy.o
CC=gcc
CFLAGS=-Wall -ansi -I./ -g 
LDFLAGS= -g -lfl
tp : $(OBJ)
	$(CC) -o tp $(OBJ) $(LDFLAGS)

tp.c :
	echo ' '

tp.o: tp.c tp_y.h tp.h
	$(CC) $(CFLAGS) -c tp.c

dummy.o: dummy.c tp_y.h tp.h
	$(CC) $(CFLAGS) -c dummy.c

print.o: print.c tp_y.h tp.h
	$(CC) $(CFLAGS) -c print.c

tp_l.o: tp_l.c tp_y.h
	$(CC) $(CFLAGS)-Wno-implicit-function-declaration -Wno-unused-function -c tp_l.c

tp_l.c : tp.l tp_y.h tp.h
	flex --yylineno -otp_l.c tp.l

tp_y.o : tp_y.c
	$(CC) $(CFLAGS) -c tp_y.c

tp_y.h tp_y.c : tp.y tp.h
	bison -v -b tp_y -o tp_y.c -d tp.y

test_lex : tp_l.c test_lex.c tp_y.h
	$(CC) $(CFLAGS) -Wno-implicit-function-declaration -Wno-unused-function -o test_lex tp_l.c test_lex.c $(LDFLAGS)

.Phony: clean

clean:
	rm -f *~ ./tp *.o tp_l.* tp_y.*
	rm -f test/*~ test/*.out test/*/*~ test/*/*.out
