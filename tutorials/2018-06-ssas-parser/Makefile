# Make file for preparing the tutorial

prepare: lib_extra_eacsl/lib_extra_eacsl.o

parser: parser.c lib_extra_eacsl/lib_extra_eacsl.o
	gcc -I lib_extra_eacsl lib_extra_eacsl/lib_extra_eacsl.o parser.c -o parser

compile: parser

.PHONY: run_test clean

run_test: parser
	printf "\001\000\024\001\000\025\001\000\060\001\001\055\001\002\000\377" | ./parser

clean:
	rm -f parser lib_extra_eacsl/lib_extra_eacsl.o

instructions/tuto.pdf instructions/tuto.html: instructions/tuto.md
	make -C instructions

distrib: tutorial_parser.tar.gz

tutorial_parser.tar.gz: $(addprefix lib_extra_eacsl/,lib_extra_eacsl.c __fc_builtin.h) parser0.c Makefile \
	$(addprefix instructions/,tuto.pdf tuto.html pandoc.css parsing.png)
	tar -cf temp.tar $^
	rm -rf tutorial_parser
	mkdir tutorial_parser
	tar -C tutorial_parser -xf temp.tar
	tar -cf $@ tutorial_parser
