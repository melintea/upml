#
#
#

FLAGS =  -ggdb -std=c++20 
FLAGS += -O0 #-O3
FLAGS += -DUPML_VERSION=0.07
#FLAGS += -DENABLE_UPML_DEBUG=1
#FLAGS += -DBOOST_SPIRIT_DEBUG=1
FLAGS += -lboost_program_options -lboost_filesystem

all:  upml

upml: *.cpp *.h* Makefile 
	g++ *.cpp $(FLAGS) -lpthread -o $@
	#clang-tidy promela_generator.cpp -- $(FLAGS) 
	
test: upml
	./_upml.sh  --file ../plantuml/syntax1.plantuml        --verify none  --diff off --ide off
	./_upml.sh  --file ../plantuml/sip/sip.plantuml        --verify both  --diff off --ide off
	./_upml.sh  --file ../plantuml/switch/switch.plantuml  --verify both  --diff off --ide off
	./_upml.sh  --file ../plantuml/hsm/hsm2.plantuml       --verify none  --diff off --ide off
	-rm pan*
	@echo "\e[42m*** Pass ***\e[0m"

lint:
	clang-tidy promela_generator.cpp -- $(FLAGS) 

clean:
	-rm *.o upml pan*
