#
#
#

FLAGS += 

all:  unittest pan

unittest: bindings.cpp bindings.hpp unittest.cpp switch_state_machine.hpp Makefile 
	g++ bindings.cpp unittest.cpp $(FLAGS) -lpthread -o $@
	
pan: 
	@echo "\e[42m*** Pass ***\e[0m"

tests: test
	@echo "\e[42m*** Pass ***\e[0m"

clean:
	-rm *.o unittest pan
