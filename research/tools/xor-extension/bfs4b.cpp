// exact sizes of 4-var functions up to level L+1, storing circuit states (sets of gate functions) up to level L
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 K; typedef uint16_t u16;
struct HS{ vector<K> t; size_t mask, n=0;
  HS(size_t cap){ size_t c=1; while(c<cap) c<<=1; t.assign(c,0); mask=c-1; }
  static size_t h(K k){ uint64_t a=(uint64_t)k, b=(uint64_t)(k>>64); a^=b*0x9E3779B97F4A7C15ULL; a^=a>>29; a*=0xBF58476D1CE4E5B9ULL; a^=a>>32; return a; }
  bool ins(K k){ size_t i=h(k)&mask; while(t[i]){ if(t[i]==k) return false; i=(i+1)&mask;} t[i]=k; n++; return true; } };
int main(int argc,char**argv){
  int L=atoi(argv[1]); const int full=65535;
  vector<int> sz(65536,-1); u16 inp[4];
  for(int i=0;i<4;i++){int t=0;for(int a=0;a<16;a++) if(a>>i&1) t|=1<<a; inp[i]=t; sz[t]=0;}
  vector<K> cur{0};
  for(int lvl=1;lvl<=L+1;lvl++){
    bool store = lvl<=L;
    size_t est = store ? cur.size()*16+1024 : 2; HS hs(est*2);
    vector<K> nxt;
    for(K s:cur){
      u16 w[12]; int nw=4; memcpy(w,inp,sizeof inp); u16 g[8]; int ng=0;
      for(K t=s;t;t>>=16){ g[ng++]=(u16)t; } for(int i=0;i<ng;i++) w[nw++]=g[i];
      auto add=[&](int v){ if(v==0||v==full) return; for(int i=0;i<nw;i++) if(w[i]==v) return; if(sz[v]<0) sz[v]=lvl;
        if(!store) return; u16 t[8]; memcpy(t,g,ng*2); t[ng]=v; sort(t,t+ng+1); K k=0; for(int i=ng;i>=0;i--) k=(k<<16)|t[i];
        if(hs.ins(k)) nxt.push_back(k); };
      for(int a=0;a<nw;a++){ add((~w[a])&full); for(int b=a+1;b<nw;b++){ add(w[a]&w[b]); add(w[a]|w[b]); } }
    }
    fprintf(stderr,"lvl %d states %zu\n",lvl,nxt.size()); cur.swap(nxt);
  }
  int X=inp[3], viol=0; map<pair<int,int>,map<int,int>> tab;
  for(int f8=1;f8<255;f8++){ int F=f8|(f8<<8), G=F^X; int cf=sz[F], cnf=sz[(~F)&full];
    if(cf<0||cnf<0) continue; int m=min(cf,cnf), M=max(cf,cnf);
    tab[{m,M}][sz[G]<0?-1:sz[G]-m]++;
    if(sz[G]>=0&&sz[G]<m+4){viol++; printf("BELOW min+4: f=%d C(f)=%d C(!f)=%d C(x^f)=%d\n",f8,cf,cnf,sz[G]);} }
  for(auto&p:tab){ printf("(%d,%d):",p.first.first,p.first.second); for(auto&q:p.second) printf(" delta%+d x%d",q.first,q.second); puts(""); }
  printf("violations of min+4: %d (delta-1 = not reached by level %d)\n",viol,L+1);
}
