/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "plantuml_parser.hpp"
#include "promela_generator.hpp"
#include "pluscal_generator.hpp"

#include <boost/filesystem.hpp>
#include <boost/program_options.hpp>

#include <cstdlib>
#include <iostream>
#include <fstream>

namespace bpo = boost::program_options;

// machine configuration options
void configure_sm(upml::sm::state_machine& sm, const bpo::variables_map& vm)
{
    //sm._config._allRandom = vm["random"].as<bool>();
}

// cat ../plantuml/t0.plantuml | ./upml
int main(int argc, char* argv[])
{
    bpo::options_description po("Plantuml state machine to spin/Promela or TLA+/PlusCal");
    bpo::variables_map       vm;

    po.add_options()
        ("help,h",         "Print usage")
        ("backend,b",      bpo::value<std::string>()->default_value("spin"), 
                           "none, spin or tla. Default: spin")
        ("in,i",           bpo::value<std::string>(), 
                           "Plantuml input file. Default: stdin")
        ("out,o",          bpo::value<std::string>(), 
                           "Backend output file. Default: stdout")
        ;

    bpo::store(bpo::parse_command_line(argc, argv, po), vm);
    if (vm.count("help"))
    {
        std::cerr << "\n" << argv[0] << ":\n" << po;
        exit(EXIT_SUCCESS);
    }

    std::ifstream  infs;
    upml::sm::id_t smTag;
    if (vm.count("in"))
    {
        const std::string& inf(vm["in"].as<std::string>());
        infs.open(inf);
        if (infs.fail())
        {
            std::cerr << inf << ": " << ::strerror(errno) << "\n";
            ::exit(EXIT_FAILURE);
        }
        smTag = boost::filesystem::path(inf).stem().c_str();
    }

    upml::sm::state_machine sm;

    bool ret =  upml::plantuml_parser(infs.is_open() ? infs : std::cin,
                                      sm);
    if ( ! ret) 
    {
        std::cerr << "plantuml parsing failed\n";
        ::exit(EXIT_FAILURE);
    }
    sm._id = smTag; //TODO: fold it in the constructor, ensure not overriden by m1

    std::ofstream  outfs;
    if (vm.count("out"))
    {
        const std::string& outf(vm["out"].as<std::string>());
        outfs.open(outf);
        if (outfs.fail())
        {
            std::cerr << outf << ": " << ::strerror(errno) << "\n";
            ::exit(EXIT_FAILURE);
        }
        outfs << "/*\n";
        for (int i=0; i<argc; ++i) {
            outfs << argv[i] <<  ' ';
        }
        outfs << "\n*/\n";
    }


    const std::string& backend(vm["backend"].as<std::string>());
    if (backend == "spin") {
        ret = ret & upml::promela_generator(outfs.is_open() ? outfs : std::cout,
                                            sm);
    } else if (backend == "tla") {
        ret = ret & upml::pluscal_generator(outfs.is_open() ? outfs : std::cout,
                                            sm);
    } else if (backend == "none") {
        ; // 
    } else {
        std::cerr << "Unsupported backend: " << backend << '\n';
        ret = EXIT_FAILURE;
    }
    
    return ret ? EXIT_SUCCESS : EXIT_FAILURE;
}

