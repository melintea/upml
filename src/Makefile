#
#
#

FLAGS = -ggdb -std=c++20 -O3

all:  upml

upml: *.cpp *.h* Makefile 
	g++ *.cpp $(FLAGS) -lpthread -o upml
	#clang-tidy promela_generator.cpp -- $(FLAGS) 

lint:
	clang-tidy promela_generator.cpp -- $(FLAGS) 

clean:
	-rm *.o upml 
