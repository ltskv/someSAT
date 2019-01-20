CFLAGS=--std=c99 -O3

NAME=somesat
OBJS=main.o

PREFIX=$(HOME)/.usr

all: $(NAME)

$(NAME): main.c
	$(CC) $(CFLAGS) -o $(NAME) main.c

clean:
	rm $(NAME)

install:
	cp $(NAME) $(PREFIX)/bin/$(NAME)

uninstall:
	rm $(PREFIX)/bin/$(NAME)
