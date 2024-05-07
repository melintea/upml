#
#
#

FLAGS =  -ggdb -std=c++20 
FLAGS += -O0 #-O3
FLAGS += -DUPML_VERSION=0.01
FLAGS += -DENABLE_UPML_DEBUG=1
FLAGS += -DBOOST_SPIRIT_DEBUG=1
FLAGS += -lboost_program_options

all:  upml

upml: *.cpp *.h* Makefile 
	g++ *.cpp $(FLAGS) -lpthread -o $@
	#clang-tidy promela_generator.cpp -- $(FLAGS) 
	
test: upml
	./upml  --backend none --in ../plantuml/t0.plantuml
	./upml --add-monitor=false --in ../plantuml/sip/sip.plantuml
	@echo "*** Pass ***"

lint:
	clang-tidy promela_generator.cpp -- $(FLAGS) 

clean:
	-rm *.o upml 
