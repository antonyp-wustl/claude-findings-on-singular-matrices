Semi-symbolic evaluation of J_4 = 8 I_alpha + 6 I_beta (main.tex, Section 4, "Exact inner integrations").
Requires Python 3 with sympy and mpmath. Run in this folder, in this order; each step takes a few minutes at most.

I_alpha
  python3 halpha.py                      # innermost (c) integral in closed form, per (a,b)-region  -> Halpha.pkl
  for r in i ii iii iv; do
    python3 bint.py $r                   # split by logarithms                                      -> parts_<r>.pkl
    python3 assemble.py $r               # b-integral in closed form (logs and dilogs)               -> G_<r>.pkl
  done
  python3 numint.py 150                  # last (a) integral by tanh-sinh quadrature, 150 digits

I_beta  (cone decomposition: I_beta = 4 * integral of beta^4 over [0,1]^3)
  python3 hbeta01.py                     # -> Hbeta01.pkl
  python3 assemble_beta.py               # -> Gbeta.pkl   (uses antider2.py)
  python3 numint_beta.py 110             # -> Ib110.txt

Identification
  python3 identify.py                    # compares the closed forms with the stored values
                                         # I_alpha_150digits.txt, I_beta_110digits.txt and re-runs PSLQ
