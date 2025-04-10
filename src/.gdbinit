set auto-load safe-path /

set breakpoint pending on

file ./upml
set args --in ../plantuml/trace/send.plantuml --backend spin
#b promela_generator.cpp:260
#b promela_generator.cpp:331a
b plantuml_parser.hpp:488

