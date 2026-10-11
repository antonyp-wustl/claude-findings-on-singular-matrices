High-precision evaluation of the two integrals defining J_4 (paper, Section 4.5).

  gcc -O3 -fopenmp -o j4dd j4dd.c -lm
  python3 nodes.py 6 n6.txt          # tanh-sinh nodes (level 6) in double-double
  ./j4dd 2 0 n6.txt                  # check: 3x3 analogue, exact value 15/2 - 5 pi^2/8
  ./j4dd 3 0 n6.txt                  # int alpha_3^4  (prints hi lo; value = hi + lo)
  ./j4dd 3 1 n6.txt                  # int beta_3^4
  python3 ref3.py 3 0                # pointwise check of the inner integral against 100-digit mpmath

J_4 = 8 * int alpha_3^4 + 6 * int beta_3^4.
Nodes with min(theta) < 1e-30 or with a product of the two smallest theta below 1e-36 are skipped;
their total weight is below 1e-30.
