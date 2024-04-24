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

size_t const static MEM_SIZE = 1 << 13;
size_t const static NUM_REGS = 8;

/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64]

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


class Cache {
public:
    Cache(const string& c_name, int c_size, int c_assoc, int c_block_size) {
        name = c_name;

        if (c_name != "dummy") {
            int num_rows = c_size / (c_assoc * c_block_size);
            print_cache_config(c_name, c_size, c_assoc, c_block_size, num_rows);
            block_size = c_block_size;
            vector<int> block(c_assoc, -1);
            rows = vector<vector<int> >(num_rows, block);
        }
    }

    void writeCache(vector<int>& curr_block, int new_tag) {
        // shift all values down 1
//        cout << "WRITE CACHE BEFORE:"<<endl;
//        for (int x: curr_block){cout << x << " " ;}
//        cout << endl;

        for (size_t idx = curr_block.size() - 1; idx > 0; idx--) {
            curr_block[idx] = curr_block[idx - 1];
        }
        curr_block[0] = new_tag;

//        cout << "WRITE CACHE AFTER:"<<endl;
//        for (int x: curr_block){cout << x << " " ;}
//        cout << endl;
    }

    string handleLW(vector<int>& curr_block, int tag_query) const{
        int target = -1;
        for (int offset = 0; offset < curr_block.size(); offset++) {//try to find a hit
            int current_shit = curr_block[offset];
            if (curr_block[offset] == tag_query) {
                target = offset;
                break;
            }
        }
        if (target > -1) { //handle hit
            int temp = curr_block[target]; // hit value

            for (int idx = target; idx > 0; idx--) {// Shift down elements to hit value in block
                curr_block[idx] = curr_block[idx - 1];
            }

            curr_block[0] = temp; // move hit value to most recent position
            return "HIT";
        }
        return "MISS";
    }

    const string& getName() const { return name; }

    string access(const string& ins, int addr, uint16_t pc) {
        string status = ins;
        // Get Parameters
        int block_id = addr / block_size;
        int row_idx = (block_id % rows.size());
        int tag_query = block_id / rows.size();

        // Index the relevant block

        if (ins == "LW") status = handleLW(rows[row_idx], tag_query);
        if (status != "HIT") writeCache(rows[row_idx], tag_query);

        print_log_entry(name, status, pc, addr, row_idx);
        return status;
    }

private:
    string name;
    int block_size;
    vector<vector<int> > rows;
};


void sim(uint16_t& pc, uint16_t regs[], uint16_t mem[], Cache& L1, Cache& L2) {

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
        uint16_t addr = (regs[rA] + imm7) & 8191;

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

            else if (opCode == 0b100) {// lw

                string L1_status = L1.access("LW", addr, pc);

                if (L1_status == "MISS" && L2.getName() == "L2") L2.access("LW", addr, pc);

                regs[rB] = mem[(regs[rA] + imm7) & 8191];
            } else if (opCode == 0b101) {// sw
                string L1_status = L1.access("SW", addr, pc);

                if (L1_status == "SW" && L2.getName() == "L2") L2.access("SW", addr, pc);

                mem[(regs[rA] + imm7) & 8191] = regs[rB];
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
//    char* filename = nullptr;
//    bool do_help = false;
//    bool arg_error = false;
//    string cache_config;
//    for (int i = 1; i < argc; i++) {
//        string arg(argv[i]);
//        if (arg.rfind("-", 0) == 0) {
//            if (arg == "-h" || arg == "--help")
//                do_help = true;
//            else if (arg == "--cache") {
//                i++;
//                if (i >= argc)
//                    arg_error = true;
//                else
//                    cache_config = argv[i];
//            } else
//                arg_error = true;
//        } else {
//            if (filename == nullptr)
//                filename = argv[i];
//            else
//                arg_error = true;
//        }
//    }
    /* Display error message if appropriate */
//    if (arg_error || do_help || filename == nullptr) {
//        cerr << "usage " << argv[0] << " [-h] [--cache CACHE] filename" << endl << endl;
//        cerr << "Simulate E20 cache" << endl << endl;
//        cerr << "positional arguments:" << endl;
//        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl << endl;
//        cerr << "optional arguments:" << endl;
//        cerr << "  -h, --help  show this help message and exit" << endl;
//        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one" << endl;
//        cerr << "                 cache) or" << endl;
//        cerr << "                 size,associativity,blocksize,size,associativity,blocksize" << endl;
//        cerr << "                 (for two caches)" << endl;
//        return 1;
//    }

//    ifstream f(filename);
    ifstream f("test.bin"); //Temp test shi
//    if (!f.is_open()) {
//        cerr << "Can't open file " << filename << endl;
//        return 1;
//    }
    load_machine_code(f, mem);


    /* parse cache config */
//    if (cache_config.size() > 0) {
//        vector<int> parts;
//        size_t pos;
//        size_t lastpos = 0;
//        while ((pos = cache_config.find(",", lastpos)) != string::npos) {
//            parts.push_back(stoi(cache_config.substr(lastpos, pos)));
//            lastpos = pos + 1;
//        }
//        parts.push_back(stoi(cache_config.substr(lastpos)));

    // L1 parts
//        int L1size = parts[0];
//        int L1assoc = parts[1];
//        int L1blocksize = parts[2];

    int L1size = 4;
    int L1assoc = 1;
    int L1blocksize = 2;
    // L2 parts
    int L2size = 8;
    int L2assoc = 4;
    int L2blocksize = 2;

    Cache L1 = Cache("L1", L1size, L1assoc, L1blocksize);
//        Cache L2 = Cache("dummy", 0, 0, 0);

//        if (parts.size() == 3) {
//            sim(pc, regArr, mem, L1, L2);
//        } else if (parts.size() == 6) {
    Cache L2 = Cache("L2", L2size, L2assoc, L2blocksize);
    sim(pc, regArr, mem, L1, L2);
//        } else {
//            cerr << "Invalid cache config" << endl;
//            return 1;
//        }
//    }
    return 0;
}
