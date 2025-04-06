all: build_lr0 build_clr1 build_slr1 build_lalr1

build_clr1: clr1/clr1_parser.cpp
	g++ clr1/clr1_parser.cpp -o clr1_parser.out -std=c++17

run_clr1: build_clr1
	./clr1_parser.out

build_lr0: lr0/lr0_parser.cpp
	g++ lr0/lr0_parser.cpp -o lr0_parser.out -std=c++17 

run_lr0: build_lr0
	./lr0_parser.out

build_slr1: slr1/slr1_parser.cpp
	g++ slr1/slr1_parser.cpp -o slr1_parser.out -std=c++17 

run_slr1: build_slr1
	./slr1_parser.out

build_lalr1: lalr1/lalr1_parser.cpp
	g++ lalr1/lalr1_parser.cpp -o lalr1_parser.out -std=c++17 

run_lalr1: build_lalr1
	./lalr1_parser.out

clean:
	rm *.out

.PHONY: clean