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

#include <boost/program_options.hpp>

#include <cstdlib>
#include <iostream>
#include <fstream>

namespace bpo = boost::program_options;

// cat ../plantuml/t0.plantuml | ./upml
int main(int argc, char* argv[])
{
    bpo::options_description po("Plantuml state machine to promela");
    bpo::variables_map       vm;

    po.add_options()
        ("help,h", "Print usage")
        ("in,i",   bpo::value<std::string>(), "Plantuml input file. Default: stdin")
        ("out,o",  bpo::value<std::string>(), "Promela output file. Default: stdout")
        ("dump,d", bpo::value<std::string>(), "Dump upml structures and maybe more")
        ;

    bpo::store(bpo::parse_command_line(argc, argv, po), vm);
    if (vm.count("help"))
    {
        std::cerr << "\n" << argv[0] << ":\n" << po;
        exit(EXIT_SUCCESS);
    }

    std::ifstream  infs;
    if (vm.count("in"))
    {
        const std::string& inf(vm["in"].as<std::string>());
        infs.open(inf);
        if (infs.fail())
        {
            std::cerr << inf << ": " << ::strerror(errno) << "\n";
            ::exit(EXIT_FAILURE);
        }
    }

    upml::sm::state_machine sm;
    
    bool ret =  upml::plantuml_parser(infs.is_open() ? infs : std::cin,
                                      sm);

    if (vm.count("dump"))
    {
        const std::string& df(vm["dump"].as<std::string>());
        std::ofstream dfs(df);
        if (dfs.fail())
        {
            std::cerr << df << ": " << ::strerror(errno) << "\n";
#ifdef ENABLE_UPML_DEBUG
            std::cerr << sm;
#endif
        }
        else
        {
            dfs << sm;
        }
    } 
    else
    {
#ifdef ENABLE_UPML_DEBUG
        //std::cerr << sm;
#endif
    }// dump

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
    }


    ret = ret & upml::promela_generator(outfs.is_open() ? outfs : std::cout,
                                        sm);
    
    return ret ? EXIT_SUCCESS : EXIT_FAILURE;
}

