// Exhaustive finite portion of the p=7 proof. C++17, standard library only.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace {
constexpr int p = 7;
constexpr int modulus = p*p;
using Word = std::array<int,p>;
using Grid = std::array<Word,p>;
using Vector = std::array<int,2>;
using Alphabet = std::array<Vector,3>;

int mod(int a,int m) { return (a%m+m)%m; }
Vector plus(Vector a,Vector b) { return {mod(a[0]+b[0],p),mod(a[1]+b[1],p)}; }

struct Vocabulary {
    Alphabet letters;
    std::vector<Word> words;
    std::vector<Word> prefixes;
    std::vector<int> necklaces;
};

// Construct the possible cyclic step words from scratch. Group words by the
// set of unordered adjacent label pairs, which is fixed across parallel lines.
std::vector<Vocabulary> vocabularies(Vector direction) {
    using Counts=std::array<int,3>;
    using Adjacencies=std::set<std::pair<int,int>>;
    std::map<std::pair<Counts,Adjacencies>,std::vector<Word>> groups;
    int wordCount=1;
    for(int i=0;i<p;++i) wordCount*=3;
    for(int code=0;code<wordCount;++code) {
        Word word;
        Counts count{};
        int value=code;
        for(int& letter:word) { letter=value%3; value/=3; ++count[letter]; }
        if(count[0]<count[1] || count[1]<count[2] || count[2]==0) continue;
        Adjacencies pairs;
        for(int i=0;i<p;++i) pairs.insert(std::minmax(word[i],word[(i+1)%p]));
        if(pairs.size()==3) groups[{count,pairs}].push_back(word);
    }
    std::vector<Vocabulary> result;
    for(const auto& entry:groups) {
        const auto& count=entry.first.first;
        for(int u=0;u<modulus;++u) for(int v=0;v<modulus;++v) {
            if(count[1]==count[2] && u>=v) continue;
            Alphabet letters={Vector{0,0},Vector{u/p,u%p},Vector{v/p,v%p}};
            auto a=letters[1],b=letters[2];
            if(mod(a[0]*b[1]-a[1]*b[0],p)==0) continue;
            bool closes=true;
            for(int k=0;k<2;++k)
                closes &= mod(direction[k]+count[1]*a[k]+count[2]*b[k],p)==0;
            if(!closes) continue;
            Vocabulary vocab{letters,entry.second,{},{}};
            for(int idx=0;idx<int(vocab.words.size());++idx) {
                Word word=vocab.words[idx],rotation=word,prefix;
                bool first=true;
                Vector offset{0,0};
                for(int i=0;i<p;++i) {
                    prefix[i]=offset[0]*p+offset[1];
                    offset=plus(offset,letters[word[i]]);
                    std::rotate(rotation.begin(),rotation.begin()+1,rotation.end());
                    if(rotation<word) first=false;
                }
                vocab.prefixes.push_back(prefix);
                if(first) vocab.necklaces.push_back(idx);
            }
            result.push_back(vocab);
        }
    }
    return result;
}

struct Automaton {
    struct Node {
        std::array<int,3> next;
        Node() { next.fill(-1); }
    };
    std::vector<Node> nodes{1};
    explicit Automaton(const Vocabulary& vocab) {
        for(const Word& word:vocab.words) {
            int node=0;
            for(int letter:word) {
                int child=nodes[node].next[letter];
                if(child==-1) {
                    child=int(nodes.size());
                    nodes[node].next[letter]=child;
                    nodes.emplace_back();
                }
                node=child;
            }
        }
    }
};

struct Counts {
    std::uint64_t sections=0,nonconstant=0;
    int minimum=std::numeric_limits<int>::max();
    int nonconstantMinimum=std::numeric_limits<int>::max();
};

// Precompute a table indexed by actual points of (Z/49Z)^2. No derivative
// cardinality formula or lower-bound shortcut is used when scoring a section.
std::vector<std::uint16_t> difference;
void prepareDifferences() {
    constexpr int size=modulus*modulus;
    difference.resize(size*size);
    for(int a=0;a<size;++a) for(int b=0;b<size;++b)
        difference[a*size+b]=mod(a/modulus-b/modulus,modulus)*modulus
                            +mod(a%modulus-b%modulus,modulus);
}

class Checker {
    struct Transition { int next; Word labels; };
    const Vocabulary& vertical;
    const Vocabulary& horizontal;
    const Automaton& automaton;
    Counts& counts;
    std::vector<std::vector<Transition>> transitions;
    Grid points{};
    std::array<int,p> columnWords{};
    std::array<std::uint64_t,modulus*modulus> seen{};

    void score() {
        ++counts.sections;
        int support=0;
        for(const auto& col:points) for(int a:col) {
            auto offset=a*modulus*modulus;
            for(const auto& col2:points) for(int b:col2) {
                auto& stamp=seen[difference[offset+b]];
                if(stamp!=counts.sections) {stamp=counts.sections; ++support;}
            }
        }
        counts.minimum=std::min(counts.minimum,support);
        if(*std::min_element(columnWords.begin(),columnWords.end())!=
           *std::max_element(columnWords.begin(),columnWords.end())) {
            ++counts.nonconstant;
            counts.nonconstantMinimum=std::min(counts.nonconstantMinimum,support);
        }
        if(support<169) {
            std::cerr<<"Counterexample, difference count "<<support<<"\n";
            for(const auto& col:points) {
                for(int a:col) std::cerr<<"("<<a/modulus<<","<<a%modulus<<") ";
                std::cerr<<"\n";
            }
            std::exit(1);
        }
    }

    void extend(int col,int word,int initial,Vector bottom,const Word& states) {
        columnWords[col]=word;
        for(int row=0;row<p;++row) {
            auto v=vertical.prefixes[word][row];
            auto lift=plus(bottom,{v/p,v%p});
            points[col][row]=(col+p*lift[0])*modulus+row+p*lift[1];
        }
        for(const auto& edge:transitions[word]) {
            if(col==p-1 && edge.next!=initial) continue;
            Word nextStates{};
            bool legal=true;
            for(int row=0;row<p;++row) {
                nextStates[row]=automaton.nodes[states[row]].next[edge.labels[row]];
                if(nextStates[row]<0) {legal=false;break;}
            }
            if(!legal) continue;
            if(col==p-1) score();
            else extend(col+1,edge.next,initial,plus(bottom,horizontal.letters[edge.labels[0]]),nextStates);
        }
    }

public:
    Checker(const Vocabulary& v,const Vocabulary& h,const Automaton& a,Counts& counts)
        :vertical(v),horizontal(h),automaton(a),counts(counts),transitions(v.words.size()) {}

    void run() {
        std::map<Vector,int> labelFor;
        for(int k=0;k<3;++k) labelFor[horizontal.letters[k]]=k;
        for(int src=0;src<int(vertical.words.size());++src)
            for(int dst=0;dst<int(vertical.words.size());++dst)
                for(const Vector& step:horizontal.letters) {
                    Transition edge{dst,{}};
                    bool legal=true;
                    for(int row=0;row<p;++row) {
                        int l=vertical.prefixes[src][row],r=vertical.prefixes[dst][row];
                        Vector d{r/p-l/p,r%p-l%p};
                        auto it=labelFor.find(plus(step,d));
                        if(it==labelFor.end()) {legal=false; break;}
                        edge.labels[row]=it->second;
                    }
                    if(legal) transitions[src].push_back(edge);
                }
        for(int first:vertical.necklaces) extend(0,first,first,{0,0},Word{});
    }
};
}

int main(int argc,char** argv) {
    auto vertical=vocabularies({0,1}),horizontal=vocabularies({1,0});
    prepareDifferences();
    std::vector<Automaton> tries;
    for(const auto& vocab:horizontal) tries.emplace_back(vocab);
    int lo=argc>1?std::stoi(argv[1]):0;
    int hi=argc>2?std::stoi(argv[2]):int(vertical.size());
    if(argc>3 || lo<0 || hi>int(vertical.size()) || lo>=hi) return 2;
    Counts counts;
    for(int i=lo;i<hi;++i) for(int j=0;j<int(horizontal.size());++j)
        Checker(vertical[i],horizontal[j],tries[j],counts).run();
    std::cout<<"families "<<vertical.size()<<" x "<<horizontal.size()<<", range "<<lo<<" "<<hi
        <<", sections "<<counts.sections<<", minimum "<<counts.minimum
        <<", varying-column sections "<<counts.nonconstant<<", varying minimum "
        <<counts.nonconstantMinimum<<"\n";
}
