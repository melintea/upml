#
#
#

FLAGS =  -ggdb -std=c++20 
FLAGS += -O0 #-O3
FLAGS += -DENABLE_AST_DEBUG=1
FLAGS += -DBOOST_SPIRIT_DEBUG=1

all:  upml

upml: *.cpp *.h* Makefile 
	g++ *.cpp $(FLAGS) -lpthread -o $@
	#clang-tidy promela_generator.cpp -- $(FLAGS) 

lint:
	clang-tidy promela_generator.cpp -- $(FLAGS) 

clean:
	-rm *.o upml 
