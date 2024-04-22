/*
CS-UY 2214
Adapted from Jeff Epstein
Starter code for E20 cache Simulator
simcache.cpp
*/
#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <iomanip>
#include <regex>
#include <cstdlib>

using namespace std;

/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64])

    @param num_rows The number of rows in the given cache.
*/
void print_cache_config(const string& cache_name, int size, int assoc, int blocksize, int num_rows) {
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
void print_log_entry(const string& cache_name, const string& status, int pc, int addr, int row) {
    cout << left << setw(8) << cache_name + " " + status << right <<
         " pc:" << setw(5) << pc <<
         "\taddr:" << setw(5) << addr <<
         "\trow:" << setw(4) << row << endl;
}

class Cache {
    struct Block {
        struct Cell {
            Cell() {
                tag = 0;
                cycle = -1;
            };
            int tag; // holds calculated tag value
            int cycle; // -1 if not accessed yet, keeps track of cycle of access
        };

        Block(int asso) { vector<Cell> cells(asso, Cell()); }

        Cell& operator[](size_t idx) { return cells[idx]; };

        int size() { return cells.size(); }

        bool full;
        vector<Cell> cells;

    };

public:
    Cache(const string& c_name, int c_size, int c_assoc, int c_block_size) {
        int num_rows = c_size / (c_assoc * c_block_size);

        name = c_name;
        size = c_size;
        asso = c_assoc;
        block_size = c_block_size;
        Block block(asso);
        rows = vector<Block>(num_rows, block);
        print_cache_config(c_name,c_size,c_assoc,c_block_size,num_rows);

    }

    int getNumRows() { return rows.size(); }

    void handleMiss(Block& curr_block, int new_tag, int cycle) {
        // Handle Miss
        size_t offset = 0;
        size_t target = 0;
        int min_cycle = -1;

        if (curr_block.full) { // Searching for LRU in full block
            for (size_t idx = 0; idx < curr_block.size(); idx++) {
                if (curr_block[offset].cycle < min_cycle) { // Find least value cycle in vector
                    min_cycle = curr_block[offset].cycle;
                    target = idx;
                }
            }
        } else
            while (target < 1) { // Searching for empty cell in not full block
                if (curr_block[offset].cycle > 0) {
                    // Find inValid Cell
                    target = offset;
                }
                offset++;
            }

        // Set LRU values or empty cell to MRU values
        curr_block[target].tag = new_tag;
        curr_block[target].cycle = cycle;
    }

    void access(int cycle, int addr, uint16_t pc) {
        cout << "HIT ACCESS" << endl;
        string status = "";
        // Get Parameters
        int block_id = addr / block_size;
        int row_idx = (block_id % rows.size());
        int tag_query = block_id / rows.size();

        cout << "Parameters:\n\tblock_id: " << block_id <<"\n\trow_idx:" << row_idx <<"\n\ttag_query:" << tag_query << endl;





        // Index the relevant block
        Block curr_block = rows[row_idx];


        for (size_t offset = 0; offset < curr_block.size(); offset++) {
            if (curr_block[offset].tag == tag_query) {
                status = "HIT"; // Update Status
                curr_block[offset].cycle = cycle; // Set New cycle
                break;
            }
        }

        if (status != "HIT") {
            status = "MISS"; // Update Status
            handleMiss(curr_block, tag_query, cycle);
        }

        print_log_entry("L1", status, pc, addr, row_idx);
    }

private:
    string name;
    int size;
    int asso;
    int block_size;
    vector<Block> rows;
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


void sim(uint16_t& pc, uint16_t regs[], uint16_t mem[], Cache& L1, Cache& L2, bool useL2) {

    bool halt = false; //Set a flag for halt instruction
    int cycle = 0;

    while (!halt) { //Continue to run until halt is flagged
        cout << cycle << endl;

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

            else if (opCode == 0b100) {
                cout << "HIT LW" << endl;
                uint16_t addr = (regs[rA] + imm7) & 8191;
                L1.access(cycle, addr, pc);


                regs[rB] = mem[(regs[rA] + imm7) & 8191];// lw
            } else if (opCode == 0b101) {
                cout << "HIT SW" << endl;

                mem[(regs[rA] + imm7) & 8191] = regs[rB];// sw
            } else if (opCode == 0b110) new_pc = regs[rA] == regs[rB] ? (pc + 1 + imm7) : pc + 1;// jeq

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
        cycle++;
    }
}


/**
    Main function
    Takes command-line args as documented below
*/
int main(int argc, char* argv[]) {

    uint16_t pc = 0;
    uint16_t regArr[NUM_REGS] = {0};
    uint16_t mem[MEM_SIZE] = {0};

    /*
        Parse the command-line arguments
    */
    char* filename = nullptr;
    bool do_help = false;
    bool arg_error = false;
    string cache_config;
    for (int i = 1; i < argc; i++) {
        string arg(argv[i]);
        if (arg.rfind("-", 0) == 0) {
            if (arg == "-h" || arg == "--help")
                do_help = true;
            else if (arg == "--cache") {
                i++;
                if (i >= argc)
                    arg_error = true;
                else
                    cache_config = argv[i];
            } else
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
        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl << endl;
        cerr << "optional arguments:" << endl;
        cerr << "  -h, --help  show this help message and exit" << endl;
        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one" << endl;
        cerr << "                 cache) or" << endl;
        cerr << "                 size,associativity,blocksize,size,associativity,blocksize" << endl;
        cerr << "                 (for two caches)" << endl;
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
            parts.push_back(stoi(cache_config.substr(lastpos, pos)));
            lastpos = pos + 1;
        }
        parts.push_back(stoi(cache_config.substr(lastpos)));

        int L1size = parts[0];
        int L1assoc = parts[1];
        int L1blocksize = parts[2];

        Cache L1 = Cache("L1", L1size, L1assoc, L1blocksize);
        print_cache_config("L1", L1size, L1assoc, L1blocksize, L1.getNumRows());

        bool useL2 = false;

        if (parts.size() == 3) {
            Cache L2 = Cache("L1", L1size, L1assoc, L1blocksize);
            sim(pc, regArr, mem, L1, L2, useL2);
        } else if (parts.size() == 6) {
            int L2size = parts[3];
            int L2assoc = parts[4];
            int L2blocksize = parts[5];
            useL2 = true;
//             TODO: execute E20 program and simulate two caches here
            Cache L2 = Cache("L2", L2size, L2assoc, L2blocksize);
            print_cache_config("L2", L2size, L2assoc, L2blocksize, L2.getNumRows());

            sim(pc, regArr, mem, L1, L2, useL2);

        } else {
            cerr << "Invalid cache config" << endl;
            return 1;
        }
    }
    return 0;
}
