#
#
#

FLAGS += -Wno-format-overflow -Wno-write-strings

all:  unittest pan

unittest: bindings.cpp bindings.hpp unittest.cpp switch_state_machine.hpp Makefile 
	g++ bindings.cpp unittest.cpp $(FLAGS) -o $@
	
pan: switch.promela bindings.cpp bindings.hpp unittest.cpp switch_state_machine.hpp Makefile 
	spin -a switch.promela 
	g++ bindings.cpp pan.c $(FLAGS) -o $@
	@echo "\e[42m*** Pass ***\e[0m"

tests: unittest pan
	./unittest
	./pan
	@echo "\e[42m*** Pass ***\e[0m"

clean:
	-rm *.o unittest pan pan.* switch.promela.trail
