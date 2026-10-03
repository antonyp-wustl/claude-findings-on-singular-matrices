import SingularMatrices.TwoByTwo

/-!
# Small cases, checked by computation

`S2` and `S3` are evaluated directly from their definitions for small `N`, and compared with
OEIS A134506 and with Appendix A of the paper.

`native_decide` runs compiled code, so these checks trust the Lean compiler as well as the
kernel. They are sanity checks of the definitions, not part of any proof.
-/

namespace SingularMatrices

/-- The possible rows `{1, …, N}³` of a 3×3 matrix. -/
abbrev rows3 (N : ℕ) : Finset (ℕ × ℕ × ℕ) := entries N ×ˢ entries N ×ˢ entries N

/-- The determinant of the 3×3 integer matrix with rows `r`, `s`, `t`. -/
def det3 (r s t : ℕ × ℕ × ℕ) : ℤ :=
  (r.1 : ℤ) * ((s.2.1 : ℤ) * t.2.2 - (s.2.2 : ℤ) * t.2.1)
    - (r.2.1 : ℤ) * ((s.1 : ℤ) * t.2.2 - (s.2.2 : ℤ) * t.1)
    + (r.2.2 : ℤ) * ((s.1 : ℤ) * t.2.1 - (s.2.1 : ℤ) * t.1)

/-- The number of singular 3×3 matrices with entries in `{1, …, N}`. -/
def S3 (N : ℕ) : ℕ :=
  ((rows3 N ×ˢ rows3 N ×ˢ rows3 N).filter (fun m => det3 m.1 m.2.1 m.2.2 = 0)).card

-- The determinant convention: det [[1,2,3],[4,5,6],[7,8,10]] = -3.
example : det3 (1, 2, 3) (4, 5, 6) (7, 8, 10) = -3 := by decide

-- 2×2: the first ten values of OEIS A134506.
example : (List.range 10).map (fun n => S2 (n + 1)) =
    [1, 6, 15, 32, 49, 86, 111, 160, 209, 278] := by
  native_decide

-- 3×3: the first four values in Appendix A of the paper.
example : (List.range 4).map (fun n => S3 (n + 1)) = [1, 248, 3975, 29104] := by
  native_decide

end SingularMatrices
