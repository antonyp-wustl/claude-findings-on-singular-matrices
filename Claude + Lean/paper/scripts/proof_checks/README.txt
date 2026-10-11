Numerical checks of the estimates in the proof of the main theorem (main.tex, Section 5).
These programs were written during the independent referee pass described in the Acknowledgments.
Compile each C program with   gcc -O2 <name>.c -o <name> -lm

./planes N LOGSIZE     Enumerates every admissible plane for the given N (via pairs of rows), with its exact
                       point count, parallel pairs and successive minima. Recomputes S_3(N) from the identity
                       of Step 1 and prints the extreme ratios for the bounds of Steps 2-3 and the error sums
                       of Step 4 divided by N^6. LOGSIZE is log2 of the hash-table size (memory 8*2^LOGSIZE
                       bytes); use 24 for N=12 and 27 for N=24. N=24 takes about 20 seconds.
                       Optional third argument 1 writes planes_dump.txt.
./fewshort R           Lemma 5.2: maximum of #{w : |w| <= R', mu_1(w) <= t} / (R'^2 t^2) over R' <= R.
./regular              Lemma 5.3: Lipschitz test of alpha near and away from the points +-e_i.
./weighted X x1 x2 ... Lemma 5.4 with phi = alpha^3: S(x) - (J/zeta(3)) log x at the checkpoints x1, x2, ...
                       (e.g. ./weighted 1200 48 192 600 1200; about 20 seconds).
./test_alpha           alpha at special directions, and J by quadrature.
python3 planar_test.py Lemma 5.1 on random lattices and convex polygons.

Results obtained (N = 12, 16, 20, 24 for ./planes):
  S_3(N) reproduced exactly: 40097796, 252273262, 1043346704, 3384786702
  max |E_w| / (N/mu_1 + 1)                    0.90, 0.96, 1.12, 1.09
  max par_P mu_1 / (L_P sqrt(3) N)  (<= 1)    0.87, 0.90, 0.91, 0.93
  min mu_1 sqrt(3) N / |w|          (>= 1)    1.028, 1.021, 1.017, 1.014
  sum N^5/(|w|^2 mu_1) / N^6                  4.66, 5.00, 5.23, 5.37
  sum N^3/mu_1^3 / N^6                        1.87, 1.92, 1.97, 1.97
  sum L_P par_P / N^6                         2.59, 2.58, 2.57, 2.65
  ./fewshort 300: max ratio 6.91;  ./regular: max 2.24;  planar_test.py: max ratio 0.37
  ./weighted: S(x) - (J/zeta(3)) log x = 8.4364, 8.4391, 8.4391, 8.4391 at x = 48, 192, 600, 1200
