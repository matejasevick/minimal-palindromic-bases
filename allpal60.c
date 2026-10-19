// allpal60: all palindromic representations of 2^n with >= 3 digits (bases 3 <= b <= 2^(n/2)), n0 <= n <= n1 <= 63. Used for (C5).
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
int main(int argc,char**argv){
  int n0=atoi(argv[1]), n1=atoi(argv[2]);
  for(int n=n0;n<=n1;n++){
    uint64_t N=1ULL<<n;
    for(uint64_t b=3; b*b<=N; b++){
      uint64_t last=N%b;
      if(last==0) continue;               // leading digit is nonzero
      // leading digit
      uint64_t t=N, p=1;
      while(t>=b){t/=b;}
      if(t!=last) continue;
      uint64_t rev=0; t=N;
      while(t){ rev=rev*b+t%b; t/=b; }
      if(rev==N) printf("PAL n=%d b=%llu\n",n,(unsigned long long)b);
    }
    fflush(stdout);
  }
}
