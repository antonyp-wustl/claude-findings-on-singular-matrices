Exact counts S_3(N) for all N <= Nmax in one pass (main.tex, Section 6.1, line-by-line formula).
  gcc -O3 -fopenmp s3all.c -o s3all
  ./s3all 100 0 200000 chunk0.txt        # arguments: Nmax, range [i0,i1) of canonical lines, output file
The program reports the number of canonical lines (v1<=v2<=v3, primitive; 141826 for Nmax=100), so the work
can be split into ranges run separately. For Nmax=100 the full run takes about 15 minutes on 4 cores.
  python3 explicit_terms.py 100 > explicit_terms.csv      # parallel-pair and axis-plane terms (Theorem 3.6)
  python3 merge_chunks.py explicit_terms.csv chunk*.txt > ../../singular_3x3_counts.csv
s3bin.c is the same computation, with the generic-plane total for N = Nmax also binned by lambda = |w|/N^2
(output lines "BIN i lo hi value"); data/bin64.txt and data/bin80{a,b,c}.txt were made with it (Figure 8).
