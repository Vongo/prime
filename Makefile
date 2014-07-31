
main: main.o
	gcc -o main main.o -lpthread -lm

main.o: main.c
	gcc -o main.o -c main.c -W -Wall