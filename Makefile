CC=clang
CFLAGS=-c -g -std=c99

NAME=somesat
OBJS=main.o

PREFIX=HOME/.usr

all: $(NAME)

main.o: main.c
	$(CC) $(CFLAGS) main.c

$(NAME): $(OBJS)
	$(CC) $(OBJS) -o $(NAME)

clean:
	rm *.o $(NAME)

install:
	cp $(NAME) $(PREFIX)/bin/$(NAME)

uninstall:
	rm $(PREFIX)/bin/$(NAME)
