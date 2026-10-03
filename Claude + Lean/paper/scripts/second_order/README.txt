The second-order constant c_3 (main.tex, Section 6.4). Compile the C programs with
  gcc -O3 -fopenmp <name>.c -o <name> -lm
The numbers they produced are collected in data/second_order_constants.txt and data/c3_table.csv.

k0.c            ./k0 X                       lattice-sum constant K0 truncated at |w| <= X (we used X = 500..4000)
deltabin.c      ./deltabin n lo stratum seed hi
                                             Haar Monte Carlo for one lambda-stratum [lo,hi] of Delta (plain estimator).
                                             For strata below lambda = 1, subtract J*log(hi/lo), J = 45 - 15 pi^2/4.
intplane.c      ./intplane N lo hi n seed    the same strata with random integer planes at a given N
hybrid.c        ./hybrid N W0 n seed         c_gen(N): planes with |w| <= W0 exactly, the rest by Monte Carlo
explicit_big.py python3 explicit_big.py M N1 N2 ...
                                             explicit terms / N^6 for large N (sieve limit M >= max N)
test2d.py       python3 test2d.py            the same framework in dimension two, compared with the exact c_2
bincmp.py       python3 bincmp.py i0 i1      per-bin comparison of exact counts (N = 64, 80), integer planes at
                                             N = 10^6 and Haar; appends to data/bincompare.jsonl (needs ./deltabin, ./intplane)
Warning: do not use 3A^2(L-A) as a control variate for the Haar averages; Var(L) diverges logarithmically.
