/*
CS-UY 2214
Adapted from Jeff Epstein
Starter code for E20 cache Simulator
simcache.cpp
*/

#include <cstddef>
#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <limits>
#include <iomanip>
#include <regex>

#include <cstdlib>


using namespace std;

struct mem_cell{
    int tag;
    int cycle;
};

size_t const static NUM_REGS = 8;
size_t const static MEM_SIZE = 1 << 13;


void load_machine_code(ifstream& f, uint16_t mem[]) {
    regex machine_code_re("^ram\\[(\\d+)\\] = 16'b(\\d+);.*$");
    size_t expectedaddr = 0;
    string line;
    while (getline(f, line)) {
        smatch sm;
        if (!regex_match(line, sm, machine_code_re)) {
            cerr << "Can't parse line: " << line << endl;
            exit(1);
        }
        size_t addr = stoi(sm[1], nullptr, 10);
        unsigned instr = stoi(sm[2], nullptr, 2);
        if (addr != expectedaddr) {
            cerr << "Memory addresses encountered out of sequence: " << addr << endl;
            exit(1);
        }
        if (addr >= MEM_SIZE) {
            cerr << "Program too big for memory" << endl;
            exit(1);
        }
        expectedaddr++;
        mem[addr] = instr;
    }
}

/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64])

    @param num_rows The number of rows in the given cache.
*/
void print_cache_config(const string &cache_name, int size, int assoc, int blocksize, int num_rows) {
    cout << "Cache " << cache_name << " has size " << size <<
        ", associativity " << assoc << ", blocksize " << blocksize <<
        ", rows " << num_rows << endl;
}

/*
    Prints out a correctly-formatted log entry.

    @param cache_name The name of the cache where the event
        occurred. "L1" or "L2"

    @param status The kind of cache event. "SW", "HIT", or
        "MISS"

    @param pc The program counter of the memory
        access instruction

    @param addr The memory address being accessed.

    @param row The cache row or set number where the data
        is stored.
*/
void print_log_entry(const string &cache_name, const string &status, int pc, int addr, int row) {
    cout << left << setw(8) << cache_name + " " + status <<  right <<
        " pc:" << setw(5) << pc <<
        "\taddr:" << setw(5) << addr <<
        "\trow:" << setw(4) << row << endl;
}


vector<vector<mem_cell> > init_cache(int assoc, int num_rows){
    mem_cell cell = {0,0};
    vector<mem_cell> block(assoc, cell);
    vector<vector<mem_cell> > new_cache (num_rows,block);
    return new_cache;
}

void sim(uint16_t& pc, uint16_t regs[], uint16_t mem[], vector<vector<mem_cell> >& L1, vector<vector<mem_cell> > & L2, bool useL2){
    bool halt = false; //Set a flag for halt instruction

    while (!halt) { //Continue to run until halt is flagged
        //Access Memory at current Program Counter
        uint16_t curr_ins = mem[pc & 8191]; //Read only 13 bits of pc

        //Breakdown Current Instruction

        //Control parameters
        uint16_t opCode = curr_ins >> 13;
        uint16_t func = curr_ins & 15;

        //Registers
        uint16_t rA = (curr_ins >> 10) & 7;
        uint16_t rB = (curr_ins >> 7) & 7;
        uint16_t rC = (curr_ins >> 4) & 7;

        //Immediate Values
        uint16_t imm7 = curr_ins & 127;
        if (imm7 & 64) imm7 |= 65408; // Sign extend 7 if its negative
        uint16_t imm13 = curr_ins & 0x1FFF; // Zero extend imm13

        //Defaulted increment of Program counter
        uint16_t new_pc = pc + 1;

        if (opCode == 0b000) {
            // Three reg instructions (add, sub, or, and, slt, jr)
            if (func == 0b0000) regs[rC] = regs[rA] + regs[rB]; // add

            else if (func == 0b0001) regs[rC] = regs[rA] - regs[rB]; // sub

            else if (func == 0b0010) regs[rC] = regs[rA] | regs[rB]; // or

            else if (func == 0b0011) regs[rC] = regs[rA] & regs[rB]; // and

            else if (func == 0b0100) regs[rC] = (regs[rA] < regs[rB]) ? 1 : 0; //slt

            else if (func == 0b1000) new_pc = regs[rA]; // jr

        } else {
            // Two reg instructions
            if (opCode == 0b001) regs[rB] = regs[rA] + imm7;// addi

            else if (opCode == 0b010) new_pc = imm13; //j

            else if (opCode == 0b100) regs[rB] = mem[(regs[rA] + imm7) & 8191];// lw

            else if (opCode == 0b101) mem[(regs[rA] + imm7) & 8191] = regs[rB];// sw

            else if (opCode == 0b110) new_pc = regs[rA] == regs[rB] ? (pc + 1 + imm7) : pc + 1;// jeq

            else if (opCode == 0b111) regs[rB] = regs[rA] < imm7;// slti

            else if (opCode == 0b011) { // jal
                regs[7] = pc + 1;
                new_pc = imm13;
            }
        }

        //Check for halt condition
        halt = (pc & 8191) == new_pc;

        // Update Program counter, if halt is false
        if (!halt) pc = new_pc;

        // Reset Rg0
        regs[0] = 0;
    }
}




/**
    Main function
    Takes command-line args as documented below
*/
int main(int argc, char *argv[]) {

    uint16_t pc = 0;
    uint16_t regArr[NUM_REGS] = {0};
    uint16_t mem[MEM_SIZE] = {0};

    /*
        Parse the command-line arguments
    */
    char *filename = nullptr;
    bool do_help = false;
    bool arg_error = false;
    string cache_config;
    for (int i=1; i<argc; i++) {
        string arg(argv[i]);
        if (arg.rfind("-",0)==0) {
            if (arg== "-h" || arg == "--help")
                do_help = true;
            else if (arg=="--cache") {
                i++;
                if (i>=argc)
                    arg_error = true;
                else
                    cache_config = argv[i];
            }
            else
                arg_error = true;
        } else {
            if (filename == nullptr)
                filename = argv[i];
            else
                arg_error = true;
        }
    }
    /* Display error message if appropriate */
    if (arg_error || do_help || filename == nullptr) {
        cerr << "usage " << argv[0] << " [-h] [--cache CACHE] filename" << endl << endl;
        cerr << "Simulate E20 cache" << endl << endl;
        cerr << "positional arguments:" << endl;
        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl<<endl;
        cerr << "optional arguments:"<<endl;
        cerr << "  -h, --help  show this help message and exit"<<endl;
        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one"<<endl;
        cerr << "                 cache) or"<<endl;
        cerr << "                 size,associativity,blocksize,size,associativity,blocksize"<<endl;
        cerr << "                 (for two caches)"<<endl;
        return 1;
    }

    ifstream f(filename);
    if (!f.is_open()) {
        cerr << "Can't open file " << filename << endl;
        return 1;
    }
    load_machine_code(f, mem);


    /* parse cache config */
    if (cache_config.size() > 0) {
        vector<int> parts;
        size_t pos;
        size_t lastpos = 0;
        while ((pos = cache_config.find(",", lastpos)) != string::npos) {
            parts.push_back(stoi(cache_config.substr(lastpos,pos)));
            lastpos = pos + 1;
        }
        parts.push_back(stoi(cache_config.substr(lastpos)));
        int L1size = parts[0];
        int L1assoc = parts[1];
        int L1blocksize = parts[2];
        int L1num_rows = L1size/ (L1assoc*L1blocksize);

        vector<vector<mem_cell> > L1 = init_cache(L1assoc,L1num_rows);
        print_cache_config("L1", L1size, L1assoc, L1blocksize, L1num_rows);

        bool useL2 = false;

        if (parts.size() == 3) {
            // TODO: execute E20 program and simulate one cache here
            vector<vector<mem_cell> > L2 = L1;
        } else if (parts.size() == 6) {
            int L2size = parts[3];
            int L2assoc = parts[4];
            int L2blocksize = parts[5];
            int L2num_rows = L2size/(L2assoc*L2blocksize);
            useL2 = true;
            // TODO: execute E20 program and simulate two caches here
            vector<vector<mem_cell> > L2 = init_cache(L2assoc,L2num_rows);
            print_cache_config("L2", L2size, L2assoc, L2blocksize, L2num_rows);

        } else {
            cerr << "Invalid cache config"  << endl;
            return 1;
        }

        sim(pc, regArr, mem,L1,L2,useL2);

    }

    return 0;
}