/* This program is free software. It comes without any warranty, to
 * the extent permitted by applicable law. You can redistribute it
 * and/or modify it under the terms of the Do What The Fuck You Want
 * To Public License, Version 2, as published by Sam Hocevar. See
 * http://sam.zoy.org/wtfpl/COPYING for more details. */ 

/*
  Author: Michael Rao
  Email: firstname dot lastname at laposte dot net   with (firstname,lastname)=(michael,rao)
*/ 

/*
  Binero / Takuzu puzzle generator. Version 0.2 (??/??/2012)

  Options: 
   -d <A> <B> : generate grids of difficulites A to B (default : 1 5)
   -s <A> <B> : generate grids of size AxA to BxB (default : 10 12)
   -n <N> : generate N grids of each difficulites  

  Difficulties from 1 to 7.
  1 : you only need to make supositions on one cell.
  2 : you need to make supositions on one line / column with 3 unkowns
  3 : you need to make supositions on one line / column with at most 4 unkowns
  4 : you need to make supositions on one line / column
  5 to 7 : you also need the "no two identical lines / columns" rule.

  To compile : g++ -O3 -o binero binero.cpp

  To generate puzzles with default options: ./binero

  Puzzles are written in the tex file "bin.tex", and solutions in "bin_sol.tex"
  There is a simple 'main.tex' file to compile with latex: 

\documentclass{article}
\usepackage{a4wide}
\usepackage{array}
\pagestyle{empty}
\begin{document}
\newlength{\collen}
\setlength{\collen}{0.4cm}
\Large
\input{bin}
\newpage
\scriptsize
\setlength{\collen}{0.17cm}
\input{bin_sol}
\end{document}

  Compile latex file into a PDF file with : pdflatex main.tex

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <list>
#include <map>
#include <string>
#include <sys/types.h>
#include <unistd.h>
#include <dirent.h> 
#include <sys/stat.h>

using namespace std;

#define NM 20
#define UNK 2

#define R_3 1
#define R_HALF 2

#define R_LINEx 16
#define R_LINE4 8
#define R_LINE3 4
#define R_LINE (4+8+16)

#define R_DUPLINES 128

#define R_ALL 255

typedef long long ll_t;

static int nbr1(unsigned long long u) {
  unsigned long long a=u-((u>>1)&0x5555555555555555LL);
  unsigned long long b=((a>>2)&0x3333333333333333LL)+(a&0x3333333333333333LL);
  unsigned long long c=((b+(b>>4 ))&0x0F0F0F0F0F0F0F0FLL);
  return (c*0x101010101010101LL)>>56;
}

#define MDIFF 7
int tdiff[MDIFF]={R_3|R_HALF,R_3|R_HALF|R_LINE3,R_3|R_HALF|R_LINE3|R_LINE4,R_3|R_HALF|R_LINE,R_3|R_HALF|R_LINE3|R_DUPLINES,R_3|R_HALF|R_LINE3|R_LINE4|R_DUPLINES,R_3|R_HALF|R_LINE|R_DUPLINES};

#define H_R 1
#define H_CTR 2
#define H_REV 8

#define S_0 16 
#define S_1 32
#define S_B 64
#define S_P 128
#define S_B3 256
#define S_S (S_0|S_1|S_B|S_P|S_B3) 

#define S_END 1024

struct score_t {
  int tab[10];
  bool operator <(const score_t &s) const {
    for(int i=9;i>=0;i--) {
      if(tab[i]<s.tab[i]) return 1;
      if(tab[i]>s.tab[i]) return 0;
    }
    return 0;
  }
  void aff(FILE *out=stdout) const {
    for(int i=0;i<MDIFF;i++) {
      fprintf(out,"%d ",tab[i]);
    }
    fprintf(out,"\n");
  }
  int diff() const {
    for(int i=9;i>=0;i--) {
      if(tab[i]) return i;
    }
    return -1;
  }
};


struct tab_t {
  int n;
  char tab[NM][NM];

  short hn0[NM];
  short hn1[NM];
  short vn0[NM];
  short vn1[NM];
  
  int hi[NM];
  int vi[NM];

  bool bad3;
  bool badH;
  bool badD;

  void init() {
    bad3=false;
    badH=false;
    badD=false;
    memset(tab,UNK,NM*NM);
    memset(hn0,0,sizeof(hn0[0])*NM);
    memset(hn1,0,sizeof(hn1[0])*NM);
    memset(vn0,0,sizeof(vn0[0])*NM);
    memset(vn1,0,sizeof(vn1[0])*NM);
    memset(hi,0,sizeof(hi[0])*NM);
    memset(vi,0,sizeof(vi[0])*NM);
  }

  void checklinecol(int i,int j) {
    int c=get(i,j);
    assert(c!=UNK);
    if(j>1) {
      if(c==get(i,j-1) && c==get(i,j-2)) {bad3=1;return;}
    } 
    if(j>0 && j<n-1) {
      if(c==get(i,j-1) && c==get(i,j+1)) {bad3=1;return;}
    } 
    if(j<n-2) {
      if(c==get(i,j+1) && c==get(i,j+2)) {bad3=1;return;}
    } 

    if(i>1) {
      if(c==get(i-1,j) && c==get(i-2,j)) {bad3=1;return;}
    } 
    if(i>0 && i<n-1) {
      if(c==get(i-1,j) && c==get(i+1,j)) {bad3=1;return;}
    } 
    if(i<n-2) {
      if(c==get(i+1,j) && c==get(i+2,j)) {bad3=1;return;}
    } 
  }

  void copywithout(const tab_t &t,int i,int j)
  {
    init();
    n=t.n;
    for(int x=0;x<n;x++)
      for(int y=0;y<n;y++)
	if(x!=i || y!=j) {
	  int c=t.get(x,y);
	  if(c!=UNK) set(x,y,c);
	}
  }
  
  void set(int i,int j,int x) {
    assert(tab[i][j]==UNK);

    tab[i][j]=x;

    if(x==0) {
      hn0[i]++;
      vn0[j]++;
      if(hn0[i]>n/2) badH=1;
      if(vn0[j]>n/2) badH=1;
    }
    if(x==1) {
      hn1[i]++;
      vn1[j]++;
      if(hn1[i]>n/2) badH=1;
      if(vn1[j]>n/2) badH=1;
      hi[i]|=(1LL<<j);
      vi[j]|=(1LL<<i);
    }
    checklinecol(i,j);
    if(bad3 || badH) return;
    if(hn0[i]+hn1[i]==n) {
      for(int k=0;k<n;k++) 
	if(k!=i && hn0[k]+hn1[k]==n) 
	  if(hi[i]==hi[k]) badD=1;
    }
    if(vn0[j]+vn1[j]==n) {
      for(int k=0;k<n;k++) 
	if(k!=j && vn0[k]+vn1[k]==n) 
	  if(vi[j]==vi[k]) badD=1;
    }
  }

  int get(int i,int j) const {
    return tab[i][j];
  }

  int hasuniquesol_() const {
    tab_t t=*this;
    {
      int i,j,x;
      while(!t.isbad() && t.findcell(i,j,x,R_3|R_HALF)) {t.set(i,j,x);}
      if(t.isbad()) return 0;
      if(t.iscomplete()) return 1;
    }
    int br=3;
    int bi=0,bj=0;
    for(int i=0;i<n;i++)
      for(int j=0;j<n;j++)
	if(t.get(i,j)==UNK) {
	  int r=0;
	  for(int x=0;x<2;x++) {
	    tab_t t2=t;
	    t2.set(i,j,x);
	    if(t2.isbad()==false) r++;
	  } 
	  if(r==0) return false;
	  if(r<br) { br=r;bi=i;bj=j;}
	}
    assert(br<3);
    int i=bi;
    int j=bj;
    int r=0;
    for(int x=0;x<2;x++) {
      tab_t t2=t;
      t2.set(i,j,x);
      if(!t2.isbad()) r+=t2.hasuniquesol_();
    }
    if(r>2) r=2;
    return r;
  }

  bool hasuniquesol() const {
    return hasuniquesol_()==1;
  }

  bool solve(int rules=R_ALL) {
    while(1) {
      if(iscomplete()) {
	assert(!isbad());
	return 1;
      }
      int i,j,x;
      bool ok=false;
      if(find(i,j,x,rules)) ok=true;
      if(ok==false) return false;
      set(i,j,x);
      assert(!isbad());
    }
  }

  ll_t nbrsol() const {
    if(isbad()) return 0;
    if(iscomplete()) {
      return 1;
    }
    for(int i=0;i<n;i++)
      for(int j=0;j<n;j++)
	if(get(i,j)==UNK) {
	  ll_t r=0;
	  tab_t t;
	  t=*this;
	  t.set(i,j,0);
	  r+=t.nbrsol();
	  t=*this;
	  t.set(i,j,1);
	  r+=t.nbrsol();
	  return r;
	}
    assert(0);
  }

  bool solvescore_(int *tab) const {
    tab_t t=*this;
    if(t.iscomplete()) {
      return 1;
    }
    int i,j,x;
    bool ok=false;
    for(int d=0;d<MDIFF;d++) {
      if(!ok && t.find(i,j,x,tdiff[d])) {tab[d]++;ok=true;}
    }
    if(!ok) return false;
    t.set(i,j,x);
    t.solvescore_(tab);
    assert(!t.isbad());
    return true;
  }

  bool solvescore(int tab[10]) const {
    memset(tab,0,sizeof(int)*10);
    return solvescore_(tab);
  }

  bool cansolve(int rules=R_ALL) const {
    tab_t t=*this;
    while(1) {
      if(t.iscomplete()) {
	assert(!t.isbad());
	return 1;
      }
      int i,j,x;
      bool ok=false;
      if(t.find(i,j,x,rules)) ok=true;
      if(ok==false) return false;
      t.set(i,j,x);
      assert(!t.isbad());
    }
  }

  void makerandlist(list<pair<int,int> > &li) {
    char tx[n*n];
    li.clear();
    memset(tx,0,n*n);
    for(int i=0;i<n*n;i++) {
      int x=rand()%(n*n-i);
      int j=0;
      while(1) {
	if(tx[j]==0) x--;
	if(x<0) break;
	j++;
      } 
      assert(j<n*n);
      tx[j]=1;
      li.push_back(make_pair(j%n,j/n));
    }
    assert(li.size()==n*n);
  }

  void centerlist(list<pair<int,int> > &li) {
    multimap<double,int> m;
    li.clear();
    for(int i=0;i<n*n;i++) {
      int a=i%n;
      int b=i/n;
      int d=(a-n/2)*(a-n/2)+(b-n/2)*(b-n/2);
      m.insert(make_pair(d+double(rand()%100)/100,i));
    }
    for(multimap<double,int>::iterator it=m.begin();it!=m.end();++it) {
      int j=it->second;
      li.push_back(make_pair(j%n,j/n));
    }
    assert(li.size()==n*n);
  }

  void filterlist(list<pair<int,int> > &li,int sel=0) {
    list<pair<int,int> > li2,li3;
    for(list<pair<int,int> >::const_iterator it=li.begin();it!=li.end();++it) {
      int i=it->first;
      int j=it->second;
      bool ok=1;
      if((sel & S_0) && get(i,j)!=0) ok=0;
      if((sel & S_1) && get(i,j)!=1) ok=0;
      if((sel & S_B) && ((i)+(j))%2!=0) ok=0;
      if((sel & S_B3) && ((i)+(j))%3==0) ok=0;
      if((sel & S_P) && (i%2!=0)) ok=0;
      if(ok)
	li2.push_back(make_pair(i,j));
      else 
	li3.push_back(make_pair(i,j));
    }
    li=li2;
    if(sel&S_END)
      for(list<pair<int,int> >::const_iterator it=li3.begin();it!=li3.end();++it) {
	li.push_back(*it);
      }
  }

  void reverselist(list<pair<int,int> > &li) {
    list<pair<int,int> > li2;
    for(list<pair<int,int> >::const_iterator it=li.begin();it!=li.end();++it) {
      int i=it->first;
      int j=it->second;
      li2.push_back(make_pair(i,j));
    }
    li=li2;
  }

  bool hasonesol(int=0) const {
    return nbrsol()==1;
  }

  bool cansolve3(int) const {
    return cansolve(R_3);
  }

  bool cansolve3h(int) const {
    return cansolve(R_3|R_HALF);
  }

  bool cansolve3hl(int) const {
    return cansolve(R_3|R_HALF|R_LINE);
  }

  bool makeonehole(bool (tab_t::*fct)(int) const,int rules,int sel=0) {
    list<pair<int,int> > li;
    if(sel&H_CTR)
      centerlist(li);
    else 
      makerandlist(li);
    if(sel&H_REV) 
      reverselist(li);
    filterlist(li,sel);
    list<pair<int,int> >::iterator it;
    for(it=li.begin();it!=li.end();++it) {
      int i=it->first;
      int j=it->second;
      if(get(i,j)==UNK) continue;
      tab_t t;
      t.copywithout(*this,i,j);
      if(0==(t.*fct)(rules)) continue;
      tab_t tmp=*this;
      this->copywithout(tmp,i,j);
      return 1;
    }
    return 0;
  } 

  bool makeonehole() {
    return makeonehole(&tab_t::hasonesol,0);
  }

  int makehole(int m) {
    for(int i=0;i<m;i++) 
      if(makeonehole()==false) return i;
    return m;
  }

  bool findcell(int &a,int &b,int &x,int rules) const {
    int rr;
    for(int i=0;i<n;i++)
      for(int j=0;j<n;j++) {
	if(get(i,j)==UNK) {
	  {
	    tab_t r=*this;
	    r.set(i,j,0);
	    if((rr=r.isbad(rules))) {a=i;b=j;x=1; return 1;}
	  }
	  {
	    tab_t r=*this;
	    r.set(i,j,1);
	    if((rr=r.isbad(rules))) {a=i;b=j;x=0; return 1;}
	  }
	}
      }
    return 0;
  }
  
 
  template<int s>
  bool findline_(int l,int &j,int &x,int rules) const {
    int n0=0,n1=0;
    int t[n];
    int p=0;
    for(int i=0;i<n;i++) {
      int c=get(s?i:l,s?l:i);
      if(c==0) n0++;
      else if(c==1) n1++;
      else if(c==UNK) t[p++]=i;
      else {assert(0);}
    }
    //printf("findline <%d> %d : n0=%d n1=%d p=%d\n",s,l,n0,n1,p);    aff();
    if(n0+n1>=n) return false;
    if(n0>n/2) return false;
    if(n1>n/2) return false;
    if(p>4 && (rules&R_LINEx)==0) return false;
    if(p>3 && (rules&R_LINE4)==0) return false;
    tab_t ta;
    int f0=0,f1=0;
    for(int k=0;k<(1LL<<p);k++) {
      //printf("k %d : %d\n",k,nbr1(k));
      if(nbr1(k)!=n/2-n1) continue;
      ta=*this;
      for(int q=0;q<p;q++) {
	ta.set(s?t[q]:l,s?l:t[q],(k>>q)&1);
      }
      //ta.aff();
      if(0==ta.isbad(rules)) {
	f1|=k;
	f0|=((1LL<<p)-1)^k;
	if(f1==(1LL<<p)-1 && f0==(1LL<<p)-1) return false;
      }
    }
    //printf("findlines <%d> %d OK : f0=%X f1=%X\n",s,l,f0,f1);    aff();
    for(int q=0;q<p;q++) {
      if((f1&(1<<q))==0) {j=t[q];x=0;assert(f0&(1<<q)); /*printf("%d %d %d\n",l,j,x);*/ return 1;}
      if((f0&(1<<q))==0) {j=t[q];x=1;assert(f1&(1<<q)); /*printf("%d %d %d\n",l,j,x);*/ return 1;}
    }
    assert(0);
  }

  bool findline(int &i,int &j,int &x,int rules) {
    for(int l=0;l<n;l++) {
      int a;
      if(findline_<0>(l,a,x,rules)) {i=l;j=a;return 1;}
      if(findline_<1>(l,a,x,rules)) {j=l;i=a;return 1;}
    }
    return false;
  }

  bool find(int &i,int &j,int &x,int rules) {
    if(findcell(i,j,x,rules)) return 1;
    if((rules & R_LINE) && findline(i,j,x,rules)) return 1;
    return false;
  }

  bool iscomplete() const {
    for(int i=0;i<n;i++) {
      if(vn0[i]+vn1[i]<n) return false;
    }
    return true;
  }

  int isbad(int rules=R_ALL) const {
    if(rules & R_3) if(bad3) return R_3;
    if(rules & R_HALF) if(badH) return R_HALF;
    if(rules & R_DUPLINES) if(badD) return R_DUPLINES;
    return 0;
  }

  void addrand()  {
    if(iscomplete()) return;
    while(1) {
      int i=rand()%n;
      int j=rand()%n;
      if(get(i,j)==UNK) {
	set(i,j,rand()%2);
	return;
      }
    }
  }
  
  bool genrand_() {
    while(!iscomplete()) {
      int i,j,x;
      while(!isbad() && findcell(i,j,x,R_3 | R_HALF)) {
	set(i,j,x);
      }
      if(isbad()) return false;
      addrand();
      if(isbad()) return false;
    }
    if(isbad()) return false;
    return true;
  }

  void genrand(int x) {
    init();
    n=x;
    while(!genrand_()) {
      init();
    }
  }

  void aff() const {
    for(int i=0;i<n;i++) {
      for(int j=0;j<n;j++) 
	printf("%c",get(i,j)!=UNK?'0'+int(get(i,j)):' ');
      printf("\n");
    }
    printf("---\n");
  }

  void afftex(FILE *out) const {
    fprintf(out,"\\begin{tabular}{");
    for(int i=0;i<n;i++) fprintf(out,"|m{\\collen}");
    fprintf(out,"|}\n\\hline\n");
    for(int i=0;i<n;i++) {
      for(int j=0;j<n;j++) 
	fprintf(out,"%c %c ",j==0?' ':'&',get(i,j)!=UNK?'0'+int(get(i,j)):' ');
      fprintf(out,"\\\\\n\\hline\n");
    }
    fprintf(out,"\\end{tabular}\n\n");
  }

  void statr(FILE *out=stdout) const {
    score_t score;
    int r=solvescore(score.tab);
    score.aff(out);
  }

  void save(FILE *out) const {
    fprintf(out,"%d\n",n);
    for(int i=0;i<n;i++) {
      for(int j=0;j<n;j++) 
	fprintf(out,"%c",get(i,j)!=UNK?'0'+int(get(i,j)):' ');
      fprintf(out,"\n");
    }
    fprintf(out,"---\n");
    statr(out);
  }
  
  bool read(FILE *in) {
    char bf[100];
    if(NULL==fgets(bf,100,in)) return 0;
    init();
    if(1!=sscanf(bf,"%d",&n)) return 0;
    for(int i=0;i<n;i++) {
      if(NULL==fgets(bf,100,in)) return 0;
      for(int j=0;(bf[j]=='0' || bf[j]=='1' || bf[j]==' ') &&j<n;j++) {
	if(bf[j]=='0') set(i,j,0);
	if(bf[j]=='1') set(i,j,1);
      }
    }
    return 1;
  }

  void save(const char *fn) const {
    FILE *o=fopen(fn,"w");
    save(o);
    fclose(o);
  }

  bool read(const char *fn) {
    FILE *o=fopen(fn,"r");
    if(!o) return 0;
    int r=read(o);
    fclose(o);
    return r;
  }

  int diff() const {
    score_t score;
    solvescore(score.tab);
    return score.diff();
  }
};

map<int,list<tab_t> > mg;

multimap<score_t,tab_t> ms; 

void t(int n,int rules,FILE *out,int sel=0)
{
  //printf("t %d %d\n", n,rules);
  tab_t tab;

  tab.genrand(n);
  
  while(1) {
    //tab.aff();tab.statr();
    if(tab.makeonehole(&tab_t::cansolve,rules,sel)==false) break;
  }

  tab.aff();
  tab.statr();

  printf("tab.diff= %d\n",tab.diff()+1);
  mg[tab.diff()].push_back(tab);

#if 0
  static int k=0;
  char fn[100];
  snprintf(fn,100,"bin_%d_%d.txt",int(getpid()),k++);
  tab.save(fn);
  
  tab_t t=tab;
#endif
}

void readall(string path,int mmax=-1) {
  int k=0;
  DIR *d=opendir(path.c_str());
  if(d==NULL) {
    printf("cannot opendir %s\n",path.c_str());
    return;
  }
  struct dirent *e;
  while(1) {
    e=readdir(d);
    if(e==NULL) break;
    if(0==strcmp(e->d_name,".")) continue;
    if(0==strcmp(e->d_name,"..")) continue;
    
    string p=path + string("/") + e->d_name;
    struct stat st;
    int r=lstat(p.c_str(),&st);
    if(r==-1) {
      printf("cannot stat %s\n",path.c_str());
    } else {
      if(S_ISDIR(st.st_mode)) {
      }
      else if(S_ISREG(st.st_mode)) {
	tab_t t;
	bool r=t.read(p.c_str());
	//if(r && t.hasonesol()==0) r=0;
	if(r) {
	  printf("%d\n",k++);
	  score_t s;

	  t.solvescore(s.tab);

#if 1
	  FILE *out=fopen("bin.tex","a");
	  fprintf(out,"\\verb!%s! ~ ",p.c_str()); 
	  s.aff(out);fprintf(out,"\\newline\n");
	  t.afftex(out);
	  fclose(out);

	  out=fopen("bin_sol.tex","a");
	  tab_t t2=t;
	  int r=t2.solve();
	  assert(r);
	  fprintf(out,"\\verb!%s! ~ ",p.c_str()); 
	  s.aff(out);fprintf(out,"\\newline\n");
	  t2.afftex(out);
	  fclose(out);
#endif

#if 0
	  ms.insert(make_pair(s,t));
#endif
#if 0	  
	  static int kk=0;
	  char fn[100];
	  snprintf(fn,100,"%d/bin_%d_%d.txt",s.diff(),int(getpid()),kk++);
	  t.save(fn);
#endif
	  //t.aff();
	  //t.statr();

	  if(k==mmax) break;
	}
      }
    }
  }
  closedir(d);
}

unsigned int nmax=10;
int sizemin=10;
int sizemax=12;
int dmin=0;
int dmax=6;

int main(int ac, char **av)
{
  int sel=0;

  while(ac>1 && av[1][0]=='-') {
    if(0==strcmp(av[1],"-n")) {nmax=atoi(av[2]); assert(nmax>0);ac-=2;av+=2;continue;}
    if(0==strcmp(av[1],"-sel")) {sel=atoi(av[2]); ac-=2;av+=2;continue;}
    if(0==strcmp(av[1],"-s")) {sizemin=atoi(av[2]);sizemax=atoi(av[3]); assert(sizemin%2==0 && sizemax%2==0); assert(sizemax>=sizemin); assert(sizemin>0); assert(sizemax<=NM); ac-=3;av+=3;continue;}
    if(0==strcmp(av[1],"-d")) {dmin=atoi(av[2])-1;dmax=atoi(av[3])-1; assert(dmin<=dmax); assert(dmin>=0); assert(dmax<MDIFF);ac-=3;av+=3;continue;}
    
    printf("unwown option : %s\n",av[1]);
    return 1;
  }
  
  if(ac>1) {
    printf("unwown option : %s\n",av[1]);
    return 1;
  }

  srand(time(NULL));
  
  int i=0;
  while(1) {
    int d;
    for(d=dmin;d<=dmax;d++) {
      if(mg[d].size()<nmax) break;
    }
    if(d<=dmax) {
      int n=sizemin+2*(i%(sizemax-sizemin+2)/2);
      t(n,tdiff[d],stdout,sel);
    } else break;
    
    i++;
  }

  int k=1;
  for(map<int,list<tab_t> >::iterator it=mg.begin();it!=mg.end();++it) {
    int nd=0;
    for(list<tab_t>::iterator it2=it->second.begin();it2!=it->second.end();++it2) {

      if(nd==nmax) break;

      tab_t t=*it2;
      
      FILE *out=fopen("bin.tex","a");
      fprintf(out,"\\# %d - Level %d ",k,it->first+1); 
      fprintf(out,"\\newline\n");
      t.afftex(out);
      fprintf(out,"\n\\medskip\n\n");
      fclose(out);
      
      out=fopen("bin_sol.tex","a");
      tab_t t2=t;
      int r=t2.solve();
      assert(r);
      fprintf(out,"\\# %d - Level %d ",k,it->first+1); 
      fprintf(out,"\\newline\n");
      t2.afftex(out);
      fprintf(out,"\n\\smallskip\n\n");
      fclose(out);
      
      k++;
      nd++;
    }
  }

  return 0;

#if 1
  readall("1",10);
  readall("2",15);
  readall("3",15);
  readall("4",15);
  readall("5",15);
  readall("6",15);
  readall("7",15);
  readall("8",15);

  for(multimap<score_t,tab_t>::iterator it=ms.begin();it!=ms.end();++it) {
    it->first.aff();
    it->second.aff();
  }
#endif

  return 0;
}
