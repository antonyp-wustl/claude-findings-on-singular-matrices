import Mathlib

/-!
# Section 5: the bookkeeping in the proof of Theorem 4.1

The proof of Theorem 4.1 combines estimates for single planes (Lemma 5.1 and Steps 2–3)
with sums over all planes (Steps 4–6). This file checks the sums. The single-plane
estimates, the count of planes with a short vector (Lemma 5.2), the exact identity of
Step 1 and the main-term asymptotics of Step 6 (Lemma 5.4) are hypotheses, stated in the
form in which the proof uses them. The conclusion (`main_bound`) is

  `|S₃(N) − (J/ζ(3)) N⁶ log N| ≤ (2c + 3 + 17000000 c³ C) N⁶`,

where `c` is the constant in the single-plane estimates and `C` the constant in Lemma 5.2.
The constant is not optimized; what matters is that it does not depend on `N`.

The proof sorts the planes into dyadic cells: plane `w` goes to the cell `(a, b)` with
`4^a ≤ |w| < 4^(a+1)` and `2^b ≤ μ₁(w) < 2^(b+1)`. Lemma 5.2 bounds the number of planes in
each cell, and the error terms of Steps 4 and 5 become geometric sums over cells.

Contents:
* `geom_le_top`, `geom_le_twice`: geometric sums.
* `sum_le_sum_cells`: bound a sum over planes by grouping the planes into cells.
* `plane_error_aux`, `uv_bound`: the error of one admissible plane (Steps 2–3).
* `cells_S1`, `cells_S2`, `step4_bound`: Step 4.
* `nonadm_bound`, `cells_A`, `cells_B`, `cells_C`, `step5_bound`: Step 5.
* `dy_pow_log_floor_le`, `dy_lt_pow_log_floor_succ`, `cell_facts`: sorting planes into cells.
* `main_bound`: Steps 1–6 combined.
-/

namespace SingularMatrices

open Finset

/-! ### Geometric sums and powers -/

/-- For `q ≥ 2`, `∑_{a < n} q^a ≤ q^n`. -/
lemma geom_le_top {q : ℝ} (hq : 2 ≤ q) (n : ℕ) : ∑ a ∈ range n, q ^ a ≤ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ q n]
    have h1 : 0 ≤ q ^ n := pow_nonneg (by linarith) n
    have h2 : 0 ≤ (q - 2) * q ^ n := mul_nonneg (by linarith) h1
    linarith

/-- For `q ≥ 2`, `K ≥ 0` and `Y ≥ 0`, the terms `K q^a ≤ Y` with `a < n` sum to at most `2Y`. -/
lemma geom_le_twice {q K Y : ℝ} (hq : 2 ≤ q) (hK : 0 ≤ K) (hY : 0 ≤ Y) (n : ℕ) :
    ∑ a ∈ (range n).filter (fun a => K * q ^ a ≤ Y), K * q ^ a ≤ 2 * Y := by
  induction n with
  | zero =>
    simp only [range_zero, filter_empty, sum_empty]
    linarith
  | succ n ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · have hall : (range n).filter (fun a => K * q ^ a ≤ Y) = range n := by
        apply filter_true_of_mem
        intro a ha
        have hpow : q ^ a ≤ q ^ n :=
          pow_le_pow_right₀ (by linarith) (le_of_lt (mem_range.mp ha))
        exact le_trans (mul_le_mul_of_nonneg_left hpow hK) h
      rw [sum_insert (by simp), hall, ← mul_sum]
      have h2 : K * ∑ a ∈ range n, q ^ a ≤ K * q ^ n :=
        mul_le_mul_of_nonneg_left (geom_le_top hq n) hK
      linarith
    · exact ih

lemma dy_four_pow (x : ℕ) : (4:ℝ) ^ x = ((2:ℝ) ^ x) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

lemma dy_sixteen_pow (x : ℕ) : (16:ℝ) ^ x = ((4:ℝ) ^ x) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-! ### Grouping a sum into cells -/

/-- The dyadic cells `(x, y)` with `x ≤ X` and `y ≤ X + 1`. -/
def dyCells (X : ℕ) : Finset (ℕ × ℕ) := range (X + 1) ×ˢ range (X + 2)

/-- Bound a sum over planes by grouping the planes into cells: if the term of each plane is
at most `φ` of its cell, and each cell holds at most `cnt` planes, then the sum is at most
`∑ cnt · φ`. -/
lemma sum_le_sum_cells {ι κ : Type*} [DecidableEq κ] (W : Finset ι) (cell : ι → κ)
    (T : Finset κ) (hT : ∀ w ∈ W, cell w ∈ T) (E : ι → ℝ) (φ cnt : κ → ℝ)
    (hE : ∀ w ∈ W, E w ≤ φ (cell w)) (hφ : ∀ p ∈ T, 0 ≤ φ p)
    (hcnt : ∀ p ∈ T, ((W.filter (fun w => cell w = p)).card : ℝ) ≤ cnt p) :
    ∑ w ∈ W, E w ≤ ∑ p ∈ T, cnt p * φ p := by
  calc ∑ w ∈ W, E w ≤ ∑ w ∈ W, φ (cell w) := sum_le_sum hE
    _ = ∑ p ∈ T, ∑ w ∈ W.filter (fun w => cell w = p), φ (cell w) :=
        (sum_fiberwise_of_maps_to hT _).symm
    _ = ∑ p ∈ T, ((W.filter (fun w => cell w = p)).card : ℝ) * φ p := by
        apply sum_congr rfl
        intro p _
        have h : ∀ w ∈ W.filter (fun w => cell w = p), φ (cell w) = φ p := by
          intro w hw
          rw [(mem_filter.mp hw).2]
        rw [sum_congr rfl h, sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ T, cnt p * φ p := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (hcnt p hp) (hφ p hp)

/-! ### One admissible plane (Steps 2 and 3) -/

/-- If `|L - M| ≤ u`, `0 ≤ par ≤ L u` and `M ≤ v`, then `|(L³ - L par) - M³| ≤ 8 (v² u + u³)`.
Here `L = L_P`, `M = M_w`, `par = par_P`, `u = c N / μ₁(w)` and `v = c N² / |w|`. -/
lemma plane_error_aux {L M par u v : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hLM : |L - M| ≤ u) (hpar0 : 0 ≤ par) (hpar : par ≤ L * u) (hMv : M ≤ v) :
    |(L ^ 3 - L * par) - M ^ 3| ≤ 8 * (v ^ 2 * u + u ^ 3) := by
  obtain ⟨e, he⟩ : ∃ e, e = |L - M| := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; exact abs_nonneg _
  have heu : e ≤ u := by rw [he]; exact hLM
  have hu0 : 0 ≤ u := le_trans he0 heu
  have hLe : L ≤ M + e := by
    have h := le_abs_self (L - M)
    rw [← he] at h
    linarith
  have hA : 0 ≤ (M + e - L) * L := mul_nonneg (by linarith) hL
  have hB : 0 ≤ (M + e - L) * (M + e) := mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ (M + e - L) * M := mul_nonneg (by linarith) hM
  have hD : 0 ≤ (M - e) ^ 2 := sq_nonneg _
  have hM0 : 0 ≤ M ^ 2 := sq_nonneg _
  have he00 : 0 ≤ e ^ 2 := sq_nonneg _
  have h1 : |L ^ 3 - M ^ 3| ≤ 6 * M ^ 2 * e + 6 * e ^ 3 := by
    have hfac : L ^ 3 - M ^ 3 = (L - M) * (L ^ 2 + L * M + M ^ 2) := by ring
    have hq : 0 ≤ L ^ 2 + L * M + M ^ 2 := by positivity
    have hq2 : L ^ 2 + L * M + M ^ 2 ≤ 6 * M ^ 2 + 6 * e ^ 2 := by linarith
    rw [hfac, abs_mul, abs_of_nonneg hq, ← he]
    calc e * (L ^ 2 + L * M + M ^ 2) ≤ e * (6 * M ^ 2 + 6 * e ^ 2) :=
          mul_le_mul_of_nonneg_left hq2 he0
      _ = 6 * M ^ 2 * e + 6 * e ^ 3 := by ring
  have h2 : L * par ≤ (2 * M ^ 2 + 2 * e ^ 2) * u := by
    have hL2 : L ^ 2 ≤ 2 * M ^ 2 + 2 * e ^ 2 := by linarith
    calc L * par ≤ L * (L * u) := mul_le_mul_of_nonneg_left hpar hL
      _ = L ^ 2 * u := by ring
      _ ≤ (2 * M ^ 2 + 2 * e ^ 2) * u := mul_le_mul_of_nonneg_right hL2 hu0
  have h3 : |(L ^ 3 - L * par) - M ^ 3| ≤ |L ^ 3 - M ^ 3| + L * par := by
    have hre : (L ^ 3 - L * par) - M ^ 3 = (L ^ 3 - M ^ 3) - L * par := by ring
    rw [hre]
    calc |(L ^ 3 - M ^ 3) - L * par| ≤ |L ^ 3 - M ^ 3| + |L * par| := abs_sub _ _
      _ = |L ^ 3 - M ^ 3| + L * par := by rw [abs_of_nonneg (mul_nonneg hL hpar0)]
  have hM2 : M ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hM hMv 2
  have he2 : e ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ he0 heu 2
  have he3 : e ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ he0 heu 3
  have a1 : M ^ 2 * e ≤ v ^ 2 * u := mul_le_mul hM2 heu he0 (sq_nonneg v)
  have a2 : M ^ 2 * u ≤ v ^ 2 * u := mul_le_mul_of_nonneg_right hM2 hu0
  have a3 : e ^ 2 * u ≤ u ^ 2 * u := mul_le_mul_of_nonneg_right he2 hu0
  linarith [h1, h2, h3, a1, a2, a3, he3]

/-- With `u = c N / μ` and `v = c N² / r`, and `R ≤ r`, `m ≤ μ`:
`v² u + u³ ≤ c³ (N⁵ / (R² m) + N³ / m³)`. -/
lemma uv_bound {c N r μ R m : ℝ} (hc : 0 ≤ c) (hN : 0 ≤ N) (hR : 0 < R) (hm : 0 < m)
    (hRr : R ≤ r) (hmμ : m ≤ μ) :
    (c * N ^ 2 / r) ^ 2 * (c * N / μ) + (c * N / μ) ^ 3
      ≤ c ^ 3 * (N ^ 5 / (R ^ 2 * m) + N ^ 3 / m ^ 3) := by
  have hr : 0 < r := lt_of_lt_of_le hR hRr
  have hμ : 0 < μ := lt_of_lt_of_le hm hmμ
  have hcN : 0 ≤ c * N := mul_nonneg hc hN
  have hcN2 : 0 ≤ c * N ^ 2 := mul_nonneg hc (pow_nonneg hN 2)
  have hu : c * N / μ ≤ c * N / m := div_le_div_of_nonneg_left hcN hm hmμ
  have hv : c * N ^ 2 / r ≤ c * N ^ 2 / R := div_le_div_of_nonneg_left hcN2 hR hRr
  have hu0 : 0 ≤ c * N / μ := div_nonneg hcN hμ.le
  have hv0 : 0 ≤ c * N ^ 2 / r := div_nonneg hcN2 hr.le
  have h1 : (c * N ^ 2 / r) ^ 2 * (c * N / μ) ≤ (c * N ^ 2 / R) ^ 2 * (c * N / m) :=
    mul_le_mul (pow_le_pow_left₀ hv0 hv 2) hu hu0 (sq_nonneg _)
  have h2 : (c * N / μ) ^ 3 ≤ (c * N / m) ^ 3 := pow_le_pow_left₀ hu0 hu 3
  have hR' : R ≠ 0 := hR.ne'
  have hm' : m ≠ 0 := hm.ne'
  have h3 : (c * N ^ 2 / R) ^ 2 * (c * N / m) + (c * N / m) ^ 3
      = c ^ 3 * (N ^ 5 / (R ^ 2 * m) + N ^ 3 / m ^ 3) := by
    first
    | ring1
    | (field_simp; ring1)
    | field_simp
  linarith

/-! ### Step 4: the admissible planes -/

/-- The cells used in Step 4: `b ≤ a + 1` (Hermite) and `4^a ≤ 4 N 2^b` (from Step 2). -/
noncomputable def T4 (N X : ℕ) : Finset (ℕ × ℕ) :=
  (dyCells X).filter (fun p => p.2 ≤ p.1 + 1 ∧ (4:ℝ) ^ p.1 ≤ 4 * N * 2 ^ p.2)

set_option maxHeartbeats 1000000 in
lemma cells_S1 (X N : ℕ) (hX : (2:ℝ) ^ X ≤ 2 * N) :
    ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1), (2:ℝ) ^ p.2 ≤ 16 * N := by
  rw [sum_filter, dyCells, sum_product]
  have h : ∀ x ∈ range (X + 1),
      ∑ y ∈ range (X + 2), (if y ≤ x + 1 then (2:ℝ) ^ y else 0) ≤ 4 * 2 ^ x := by
    intro x hx
    have hx' : x ≤ X := by have := mem_range.mp hx; omega
    rw [← sum_filter]
    have e : (range (X + 2)).filter (fun y => y ≤ x + 1) = range (x + 2) := by
      ext y
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨_, hy⟩
        omega
      · intro hy
        constructor <;> omega
    rw [e]
    calc ∑ y ∈ range (x + 2), (2:ℝ) ^ y ≤ 2 ^ (x + 2) := geom_le_top (by norm_num) _
      _ = 4 * 2 ^ x := by ring
  calc ∑ x ∈ range (X + 1), ∑ y ∈ range (X + 2), (if y ≤ x + 1 then (2:ℝ) ^ y else 0)
      ≤ ∑ x ∈ range (X + 1), 4 * (2:ℝ) ^ x := sum_le_sum h
    _ = 4 * ∑ x ∈ range (X + 1), (2:ℝ) ^ x := by rw [mul_sum]
    _ ≤ 4 * 2 ^ (X + 1) :=
        mul_le_mul_of_nonneg_left (geom_le_top (by norm_num) _) (by norm_num)
    _ = 8 * 2 ^ X := by ring
    _ ≤ 16 * N := by linarith

set_option maxHeartbeats 1000000 in
lemma cells_S2 (X N : ℕ) (hX : (2:ℝ) ^ X ≤ 2 * N) :
    ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => (4:ℝ) ^ p.1 ≤ 4 * N * 2 ^ p.2),
      ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 ≤ 256 * (N:ℝ) ^ 3 := by
  rw [sum_filter, dyCells, sum_product_right]
  have h : ∀ y ∈ range (X + 2),
      ∑ x ∈ range (X + 1), (if (4:ℝ) ^ x ≤ 4 * N * 2 ^ y then ((4:ℝ) ^ x) ^ 2 / 2 ^ y else 0)
        ≤ 32 * (N:ℝ) ^ 2 * 2 ^ y := by
    intro y _
    have h2y : (2:ℝ) ^ y ≠ 0 := by positivity
    rw [← sum_filter, ← sum_div]
    have hsub : ∑ x ∈ (range (X + 1)).filter (fun x => (4:ℝ) ^ x ≤ 4 * N * 2 ^ y),
        ((4:ℝ) ^ x) ^ 2 ≤ 2 * (4 * (N:ℝ) * 2 ^ y) ^ 2 := by
      calc ∑ x ∈ (range (X + 1)).filter (fun x => (4:ℝ) ^ x ≤ 4 * N * 2 ^ y), ((4:ℝ) ^ x) ^ 2
          = ∑ x ∈ (range (X + 1)).filter (fun x => (4:ℝ) ^ x ≤ 4 * N * 2 ^ y),
              1 * (16:ℝ) ^ x := by
            apply sum_congr rfl
            intro x _
            rw [one_mul, dy_sixteen_pow x]
        _ ≤ ∑ x ∈ (range (X + 1)).filter
              (fun x => 1 * (16:ℝ) ^ x ≤ (4 * (N:ℝ) * 2 ^ y) ^ 2), 1 * (16:ℝ) ^ x := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [mem_filter] at hx ⊢
              refine ⟨hx.1, ?_⟩
              rw [one_mul, dy_sixteen_pow x]
              exact pow_le_pow_left₀ (by positivity) hx.2 2
            · intro x _ _
              positivity
        _ ≤ 2 * (4 * (N:ℝ) * 2 ^ y) ^ 2 :=
            geom_le_twice (by norm_num) (by norm_num) (by positivity) _
    calc (∑ x ∈ (range (X + 1)).filter (fun x => (4:ℝ) ^ x ≤ 4 * N * 2 ^ y),
          ((4:ℝ) ^ x) ^ 2) / 2 ^ y
        ≤ 2 * (4 * (N:ℝ) * 2 ^ y) ^ 2 / 2 ^ y :=
          div_le_div_of_nonneg_right hsub (by positivity)
      _ = 32 * (N:ℝ) ^ 2 * 2 ^ y := by
          rw [div_eq_iff h2y]
          ring
  calc ∑ y ∈ range (X + 2), ∑ x ∈ range (X + 1),
        (if (4:ℝ) ^ x ≤ 4 * N * 2 ^ y then ((4:ℝ) ^ x) ^ 2 / 2 ^ y else 0)
      ≤ ∑ y ∈ range (X + 2), 32 * (N:ℝ) ^ 2 * 2 ^ y := sum_le_sum h
    _ = 32 * (N:ℝ) ^ 2 * ∑ y ∈ range (X + 2), (2:ℝ) ^ y := by rw [mul_sum]
    _ ≤ 32 * (N:ℝ) ^ 2 * 2 ^ (X + 2) :=
        mul_le_mul_of_nonneg_left (geom_le_top (by norm_num) _) (by positivity)
    _ = 128 * (N:ℝ) ^ 2 * 2 ^ X := by ring
    _ ≤ 128 * (N:ℝ) ^ 2 * (2 * N) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 256 * (N:ℝ) ^ 3 := by ring

set_option maxHeartbeats 1000000 in
/-- **Step 4.** Given the single-plane estimates of Steps 2–3, and at most
`C (4^a)² (2^b)²` admissible planes in each cell `(a, b)`, the errors of the admissible
planes sum to at most `2176 c³ C N⁶`. -/
theorem step4_bound {ι : Type*} (W : Finset ι) {N X : ℕ} (hX : (2:ℝ) ^ X ≤ 2 * N)
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (L M par r μ : ι → ℝ) (a b : ι → ℕ)
    (hL : ∀ w ∈ W, 0 ≤ L w) (hM : ∀ w ∈ W, 0 ≤ M w)
    (hLM : ∀ w ∈ W, |L w - M w| ≤ c * N / μ w)
    (hpar0 : ∀ w ∈ W, 0 ≤ par w) (hpar : ∀ w ∈ W, par w ≤ c * L w * N / μ w)
    (hMr : ∀ w ∈ W, M w ≤ c * N ^ 2 / r w)
    (hra : ∀ w ∈ W, (4:ℝ) ^ a w ≤ r w) (hμb : ∀ w ∈ W, (2:ℝ) ^ b w ≤ μ w)
    (haX : ∀ w ∈ W, a w ≤ X) (hHerm : ∀ w ∈ W, b w ≤ a w + 1)
    (hlow : ∀ w ∈ W, (4:ℝ) ^ a w ≤ 4 * N * 2 ^ b w)
    (hcount : ∀ p ∈ T4 N X, ((W.filter (fun w => (a w, b w) = p)).card : ℝ) ≤
      C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) :
    ∑ w ∈ W, |(L w ^ 3 - L w * par w) - M w ^ 3| ≤ 2176 * c ^ 3 * C * (N:ℝ) ^ 6 := by
  have hA := sum_le_sum_cells W (fun w => (a w, b w)) (T4 N X)
    (fun w hw => by
      have h1 := haX w hw
      have h2 := hHerm w hw
      simp only [T4, dyCells, mem_filter, mem_product, mem_range]
      exact ⟨⟨by omega, by omega⟩, h2, hlow w hw⟩)
    (fun w => |(L w ^ 3 - L w * par w) - M w ^ 3|)
    (fun p => 8 * c ^ 3 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2) +
      (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3))
    (fun p => C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2)
    (fun w hw => by
      have hr4 : (0:ℝ) < 4 ^ a w := by positivity
      have hm2 : (0:ℝ) < 2 ^ b w := by positivity
      have hpar' : par w ≤ L w * (c * N / μ w) := by
        calc par w ≤ c * L w * N / μ w := hpar w hw
          _ = L w * (c * N / μ w) := by ring
      have h1 := plane_error_aux (hL w hw) (hM w hw) (hLM w hw) (hpar0 w hw) hpar' (hMr w hw)
      have h2 := uv_bound hc (Nat.cast_nonneg N) hr4 hm2 (hra w hw) (hμb w hw)
      show |(L w ^ 3 - L w * par w) - M w ^ 3| ≤
        8 * c ^ 3 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ a w) ^ 2 * 2 ^ b w) + (N:ℝ) ^ 3 / ((2:ℝ) ^ b w) ^ 3)
      linarith)
    (fun p _ => by
      have h1 : (0:ℝ) ≤ (N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2) +
          (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3 := by positivity
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc 3)) h1)
    hcount
  have hterm : ∀ p ∈ T4 N X,
      C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
        (8 * c ^ 3 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2) +
          (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3))
      = 8 * c ^ 3 * C * ((N:ℝ) ^ 5 * 2 ^ p.2 + (N:ℝ) ^ 3 * (((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2)) := by
    intro p _
    have h42 : ((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2 ≠ 0 := by positivity
    have h2 : (2:ℝ) ^ p.2 ≠ 0 := by positivity
    have h23 : ((2:ℝ) ^ p.2) ^ 3 ≠ 0 := by positivity
    have e1 : ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2))
        = (N:ℝ) ^ 5 * 2 ^ p.2 := by
      rw [mul_div_assoc', div_eq_iff h42]
      ring
    have e2 : ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 * ((N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3)
        = (N:ℝ) ^ 3 * (((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) := by
      rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff h23 h2]
      ring
    calc C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
          (8 * c ^ 3 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2) +
            (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3))
        = 8 * c ^ 3 * C * (((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
              ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2)) +
            ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 * ((N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3)) := by
          ring
      _ = 8 * c ^ 3 * C * ((N:ℝ) ^ 5 * 2 ^ p.2 + (N:ℝ) ^ 3 * (((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2)) := by
          rw [e1, e2]
  have hsub1 : T4 N X ⊆ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1) := by
    intro p hp
    simp only [T4, mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hsub2 : T4 N X ⊆
      (dyCells X).filter (fun p : ℕ × ℕ => (4:ℝ) ^ p.1 ≤ 4 * N * 2 ^ p.2) := by
    intro p hp
    simp only [T4, mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have hS1 : ∑ p ∈ T4 N X, (2:ℝ) ^ p.2 ≤ 16 * N :=
    le_trans (sum_le_sum_of_subset_of_nonneg hsub1 (fun p _ _ => by positivity))
      (cells_S1 X N hX)
  have hS2 : ∑ p ∈ T4 N X, ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 ≤ 256 * (N:ℝ) ^ 3 :=
    le_trans (sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity))
      (cells_S2 X N hX)
  have hk : 0 ≤ 8 * c ^ 3 * C := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc 3)) hC
  calc ∑ w ∈ W, |(L w ^ 3 - L w * par w) - M w ^ 3|
      ≤ ∑ p ∈ T4 N X, C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
          (8 * c ^ 3 * ((N:ℝ) ^ 5 / (((4:ℝ) ^ p.1) ^ 2 * 2 ^ p.2) +
            (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3)) := hA
    _ = ∑ p ∈ T4 N X, 8 * c ^ 3 * C * ((N:ℝ) ^ 5 * 2 ^ p.2 +
          (N:ℝ) ^ 3 * (((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2)) := sum_congr rfl hterm
    _ = 8 * c ^ 3 * C * ((N:ℝ) ^ 5 * ∑ p ∈ T4 N X, (2:ℝ) ^ p.2 +
          (N:ℝ) ^ 3 * ∑ p ∈ T4 N X, ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 8 * c ^ 3 * C * ((N:ℝ) ^ 5 * (16 * N) + (N:ℝ) ^ 3 * (256 * (N:ℝ) ^ 3)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hk
        · exact mul_le_mul_of_nonneg_left hS1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = 2176 * c ^ 3 * C * (N:ℝ) ^ 6 := by ring

/-! ### Step 5: the other non-admissible planes -/

lemma dy_cube_add_one_le {s : ℝ} (hs : 0 ≤ s) : (s + 1) ^ 3 ≤ 4 * (s ^ 3 + 1) := by
  linarith [mul_nonneg (sq_nonneg (s - 1)) (by linarith : (0:ℝ) ≤ s + 1)]

/-- A non-admissible plane with `M ≤ c N² / r` and `M ≤ c (N / μ + 1)`: in a cell with
`N m ≤ R` use the first bound, otherwise the second. -/
lemma nonadm_bound {c N M r μ R m : ℝ} (hc : 0 ≤ c) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hR : 0 < R) (hm : 0 < m) (hRr : R ≤ r) (hmμ : m ≤ μ)
    (hM1 : M ≤ c * N ^ 2 / r) (hM2 : M ≤ c * (N / μ + 1)) :
    M ^ 3 ≤ 4 * c ^ 3 * ((if N * m ≤ R then N ^ 6 / R ^ 3 else N ^ 3 / m ^ 3) + 1) := by
  have hR' : R ≠ 0 := hR.ne'
  have hm' : m ≠ 0 := hm.ne'
  have hc3 : 0 ≤ c ^ 3 := pow_nonneg hc 3
  split_ifs with h
  · have h1 : M ≤ c * N ^ 2 / R :=
      le_trans hM1 (div_le_div_of_nonneg_left (mul_nonneg hc (pow_nonneg hN 2)) hR hRr)
    have h2 : M ^ 3 ≤ (c * N ^ 2 / R) ^ 3 := pow_le_pow_left₀ hM h1 3
    have h3 : (c * N ^ 2 / R) ^ 3 = c ^ 3 * (N ^ 6 / R ^ 3) := by
      first
      | ring1
      | (field_simp; ring1)
      | field_simp
    have h4 : 0 ≤ c ^ 3 * (N ^ 6 / R ^ 3) :=
      mul_nonneg hc3 (div_nonneg (pow_nonneg hN 6) (pow_nonneg hR.le 3))
    linarith
  · have h1 : M ≤ c * (N / m + 1) := by
      refine le_trans hM2 (mul_le_mul_of_nonneg_left ?_ hc)
      have : N / μ ≤ N / m := div_le_div_of_nonneg_left hN hm hmμ
      linarith
    have hs : 0 ≤ N / m := div_nonneg hN hm.le
    have h2 : M ^ 3 ≤ (c * (N / m + 1)) ^ 3 := pow_le_pow_left₀ hM h1 3
    have h4 : c ^ 3 * (N / m + 1) ^ 3 ≤ c ^ 3 * (4 * ((N / m) ^ 3 + 1)) :=
      mul_le_mul_of_nonneg_left (dy_cube_add_one_le hs) hc3
    calc M ^ 3 ≤ (c * (N / m + 1)) ^ 3 := h2
      _ = c ^ 3 * (N / m + 1) ^ 3 := by ring
      _ ≤ c ^ 3 * (4 * ((N / m) ^ 3 + 1)) := h4
      _ = 4 * c ^ 3 * (N ^ 3 / m ^ 3 + 1) := by rw [div_pow]; ring

set_option maxHeartbeats 1000000 in
lemma cells_A (X N : ℕ) (hX : (2:ℝ) ^ X ≤ 2 * N) :
    ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1),
      (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1 ≤ 32 * (N:ℝ) ^ 6 := by
  rw [sum_filter, dyCells, sum_product]
  have h : ∀ x ∈ range (X + 1),
      ∑ y ∈ range (X + 2), (if (N:ℝ) * 2 ^ y ≤ 4 ^ x then
        (N:ℝ) ^ 6 * ((2:ℝ) ^ y) ^ 2 / 4 ^ x else 0) ≤ 2 * (N:ℝ) ^ 4 * 4 ^ x := by
    intro x _
    have h4x : (4:ℝ) ^ x ≠ 0 := by positivity
    rw [← sum_filter]
    have heq : ∀ y ∈ (range (X + 2)).filter (fun y => (N:ℝ) * 2 ^ y ≤ 4 ^ x),
        (N:ℝ) ^ 6 * ((2:ℝ) ^ y) ^ 2 / 4 ^ x = (N:ℝ) ^ 4 / 4 ^ x * ((N:ℝ) ^ 2 * 4 ^ y) := by
      intro y _
      rw [dy_four_pow y]
      ring
    rw [sum_congr rfl heq, ← mul_sum]
    have hsub : ∑ y ∈ (range (X + 2)).filter (fun y => (N:ℝ) * 2 ^ y ≤ 4 ^ x),
        (N:ℝ) ^ 2 * 4 ^ y ≤ 2 * ((4:ℝ) ^ x) ^ 2 := by
      calc ∑ y ∈ (range (X + 2)).filter (fun y => (N:ℝ) * 2 ^ y ≤ 4 ^ x), (N:ℝ) ^ 2 * 4 ^ y
          ≤ ∑ y ∈ (range (X + 2)).filter
              (fun y => (N:ℝ) ^ 2 * 4 ^ y ≤ ((4:ℝ) ^ x) ^ 2), (N:ℝ) ^ 2 * 4 ^ y := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro y hy
              rw [mem_filter] at hy ⊢
              refine ⟨hy.1, ?_⟩
              have h0 : (0:ℝ) ≤ N * 2 ^ y := by positivity
              have h1 := pow_le_pow_left₀ h0 hy.2 2
              calc (N:ℝ) ^ 2 * 4 ^ y = ((N:ℝ) * 2 ^ y) ^ 2 := by rw [dy_four_pow y]; ring
                _ ≤ ((4:ℝ) ^ x) ^ 2 := h1
            · intro y _ _
              positivity
        _ ≤ 2 * ((4:ℝ) ^ x) ^ 2 :=
            geom_le_twice (by norm_num) (by positivity) (by positivity) _
    calc (N:ℝ) ^ 4 / 4 ^ x * ∑ y ∈ (range (X + 2)).filter (fun y => (N:ℝ) * 2 ^ y ≤ 4 ^ x),
          (N:ℝ) ^ 2 * 4 ^ y
        ≤ (N:ℝ) ^ 4 / 4 ^ x * (2 * ((4:ℝ) ^ x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 2 * (N:ℝ) ^ 4 * 4 ^ x := by
          rw [div_mul_eq_mul_div, div_eq_iff h4x]
          ring
  have e4 : (4:ℝ) ^ (X + 1) = 4 * ((2:ℝ) ^ X) ^ 2 := by
    rw [pow_succ (4:ℝ) X, dy_four_pow X]
    ring
  calc ∑ x ∈ range (X + 1), ∑ y ∈ range (X + 2), (if (N:ℝ) * 2 ^ y ≤ 4 ^ x then
        (N:ℝ) ^ 6 * ((2:ℝ) ^ y) ^ 2 / 4 ^ x else 0)
      ≤ ∑ x ∈ range (X + 1), 2 * (N:ℝ) ^ 4 * 4 ^ x := sum_le_sum h
    _ = 2 * (N:ℝ) ^ 4 * ∑ x ∈ range (X + 1), (4:ℝ) ^ x := by rw [mul_sum]
    _ ≤ 2 * (N:ℝ) ^ 4 * 4 ^ (X + 1) :=
        mul_le_mul_of_nonneg_left (geom_le_top (by norm_num) _) (by positivity)
    _ = 8 * (N:ℝ) ^ 4 * ((2:ℝ) ^ X) ^ 2 := by rw [e4]; ring
    _ ≤ 8 * (N:ℝ) ^ 4 * (2 * N) ^ 2 := by
        have h0 : (0:ℝ) ≤ 2 ^ X := by positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hX 2) (by positivity)
    _ = 32 * (N:ℝ) ^ 6 := by ring

set_option maxHeartbeats 1000000 in
lemma cells_B (X N : ℕ) (hX : (2:ℝ) ^ X ≤ 2 * N) :
    ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => ¬ ((N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1)),
      (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 ≤ 16 * (N:ℝ) ^ 6 := by
  rw [sum_filter, dyCells, sum_product_right]
  have h : ∀ y ∈ range (X + 2),
      ∑ x ∈ range (X + 1), (if ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x) then
        (N:ℝ) ^ 3 * ((4:ℝ) ^ x) ^ 2 / 2 ^ y else 0) ≤ 2 * (N:ℝ) ^ 5 * 2 ^ y := by
    intro y _
    have h2y : (2:ℝ) ^ y ≠ 0 := by positivity
    rw [← sum_filter]
    have heq : ∀ x ∈ (range (X + 1)).filter (fun x => ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x)),
        (N:ℝ) ^ 3 * ((4:ℝ) ^ x) ^ 2 / 2 ^ y = (N:ℝ) ^ 3 / 2 ^ y * (1 * (16:ℝ) ^ x) := by
      intro x _
      rw [dy_sixteen_pow x]
      ring
    rw [sum_congr rfl heq, ← mul_sum]
    have hsub : ∑ x ∈ (range (X + 1)).filter (fun x => ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x)),
        1 * (16:ℝ) ^ x ≤ 2 * ((N:ℝ) * 2 ^ y) ^ 2 := by
      calc ∑ x ∈ (range (X + 1)).filter (fun x => ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x)), 1 * (16:ℝ) ^ x
          ≤ ∑ x ∈ (range (X + 1)).filter
              (fun x => 1 * (16:ℝ) ^ x ≤ ((N:ℝ) * 2 ^ y) ^ 2), 1 * (16:ℝ) ^ x := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [mem_filter] at hx ⊢
              refine ⟨hx.1, ?_⟩
              have hlt : (4:ℝ) ^ x < N * 2 ^ y := not_le.mp hx.2
              rw [one_mul, dy_sixteen_pow x]
              exact pow_le_pow_left₀ (by positivity) hlt.le 2
            · intro x _ _
              positivity
        _ ≤ 2 * ((N:ℝ) * 2 ^ y) ^ 2 :=
            geom_le_twice (by norm_num) (by norm_num) (by positivity) _
    calc (N:ℝ) ^ 3 / 2 ^ y * ∑ x ∈ (range (X + 1)).filter
          (fun x => ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x)), 1 * (16:ℝ) ^ x
        ≤ (N:ℝ) ^ 3 / 2 ^ y * (2 * ((N:ℝ) * 2 ^ y) ^ 2) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 2 * (N:ℝ) ^ 5 * 2 ^ y := by
          rw [div_mul_eq_mul_div, div_eq_iff h2y]
          ring
  calc ∑ y ∈ range (X + 2), ∑ x ∈ range (X + 1), (if ¬ ((N:ℝ) * 2 ^ y ≤ 4 ^ x) then
        (N:ℝ) ^ 3 * ((4:ℝ) ^ x) ^ 2 / 2 ^ y else 0)
      ≤ ∑ y ∈ range (X + 2), 2 * (N:ℝ) ^ 5 * 2 ^ y := sum_le_sum h
    _ = 2 * (N:ℝ) ^ 5 * ∑ y ∈ range (X + 2), (2:ℝ) ^ y := by rw [mul_sum]
    _ ≤ 2 * (N:ℝ) ^ 5 * 2 ^ (X + 2) :=
        mul_le_mul_of_nonneg_left (geom_le_top (by norm_num) _) (by positivity)
    _ = 8 * (N:ℝ) ^ 5 * 2 ^ X := by ring
    _ ≤ 8 * (N:ℝ) ^ 5 * (2 * N) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 16 * (N:ℝ) ^ 6 := by ring

set_option maxHeartbeats 1000000 in
lemma cells_C (X N : ℕ) (hX : (2:ℝ) ^ X ≤ 2 * N) :
    ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
      ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 ≤ 65536 * (N:ℝ) ^ 6 := by
  rw [sum_filter, dyCells, sum_product]
  have h : ∀ x ∈ range (X + 1),
      ∑ y ∈ range (X + 2), (if y ≤ x + 1 then ((4:ℝ) ^ x) ^ 2 * ((2:ℝ) ^ y) ^ 2 else 0)
        ≤ 16 * (64:ℝ) ^ x := by
    intro x hx
    have hx' : x ≤ X := by have := mem_range.mp hx; omega
    rw [← sum_filter]
    have e : (range (X + 2)).filter (fun y => y ≤ x + 1) = range (x + 2) := by
      ext y
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨_, hy⟩
        omega
      · intro hy
        constructor <;> omega
    rw [e, ← mul_sum]
    have hg : ∑ y ∈ range (x + 2), ((2:ℝ) ^ y) ^ 2 ≤ 4 ^ (x + 2) := by
      calc ∑ y ∈ range (x + 2), ((2:ℝ) ^ y) ^ 2 = ∑ y ∈ range (x + 2), (4:ℝ) ^ y := by
            apply sum_congr rfl
            intro y _
            rw [dy_four_pow y]
        _ ≤ 4 ^ (x + 2) := geom_le_top (by norm_num) _
    have e64 : (64:ℝ) ^ x = ((4:ℝ) ^ x) ^ 2 * 4 ^ x := by
      rw [← dy_sixteen_pow x, ← mul_pow]
      norm_num
    calc ((4:ℝ) ^ x) ^ 2 * ∑ y ∈ range (x + 2), ((2:ℝ) ^ y) ^ 2
        ≤ ((4:ℝ) ^ x) ^ 2 * 4 ^ (x + 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 16 * (64:ℝ) ^ x := by
          rw [e64, pow_add (4:ℝ) x 2]
          ring
  have e64 : (64:ℝ) ^ (X + 1) = 64 * ((2:ℝ) ^ X) ^ 6 := by
    have h1 : (64:ℝ) ^ X = ((2:ℝ) ^ X) ^ 6 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [pow_succ (64:ℝ) X, h1]
    ring
  calc ∑ x ∈ range (X + 1), ∑ y ∈ range (X + 2),
        (if y ≤ x + 1 then ((4:ℝ) ^ x) ^ 2 * ((2:ℝ) ^ y) ^ 2 else 0)
      ≤ ∑ x ∈ range (X + 1), 16 * (64:ℝ) ^ x := sum_le_sum h
    _ = 16 * ∑ x ∈ range (X + 1), (64:ℝ) ^ x := by rw [mul_sum]
    _ ≤ 16 * 64 ^ (X + 1) :=
        mul_le_mul_of_nonneg_left (geom_le_top (by norm_num) _) (by norm_num)
    _ = 1024 * ((2:ℝ) ^ X) ^ 6 := by rw [e64]; ring
    _ ≤ 1024 * (2 * (N:ℝ)) ^ 6 := by
        have h0 : (0:ℝ) ≤ 2 ^ X := by positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hX 6) (by norm_num)
    _ = 65536 * (N:ℝ) ^ 6 := by ring

set_option maxHeartbeats 1000000 in
/-- **Step 5.** Non-admissible planes other than the coordinate planes, with
`M ≤ c N² / |w|` and `M ≤ c (N / μ₁ + 1)`, and at most `C (4^a)² (2^b)²` of them in each
cell `(a, b)`, contribute at most `262336 c³ C N⁶`. -/
theorem step5_bound {ι : Type*} (W : Finset ι) {N X : ℕ} (hX : (2:ℝ) ^ X ≤ 2 * N)
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (M r μ : ι → ℝ) (a b : ι → ℕ)
    (hM : ∀ w ∈ W, 0 ≤ M w) (hM1 : ∀ w ∈ W, M w ≤ c * N ^ 2 / r w)
    (hM2 : ∀ w ∈ W, M w ≤ c * (N / μ w + 1))
    (hra : ∀ w ∈ W, (4:ℝ) ^ a w ≤ r w) (hμb : ∀ w ∈ W, (2:ℝ) ^ b w ≤ μ w)
    (haX : ∀ w ∈ W, a w ≤ X) (hHerm : ∀ w ∈ W, b w ≤ a w + 1)
    (hcount : ∀ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
      ((W.filter (fun w => (a w, b w) = p)).card : ℝ) ≤
        C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) :
    ∑ w ∈ W, M w ^ 3 ≤ 262336 * c ^ 3 * C * (N:ℝ) ^ 6 := by
  have hA := sum_le_sum_cells W (fun w => (a w, b w))
    ((dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1))
    (fun w hw => by
      have h1 := haX w hw
      have h2 := hHerm w hw
      simp only [dyCells, mem_filter, mem_product, mem_range]
      exact ⟨⟨by omega, by omega⟩, h2⟩)
    (fun w => M w ^ 3)
    (fun p => 4 * c ^ 3 * ((if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3
      else (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3) + 1))
    (fun p => C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2)
    (fun w hw => by
      have hr4 : (0:ℝ) < 4 ^ a w := by positivity
      have hm2 : (0:ℝ) < 2 ^ b w := by positivity
      exact nonadm_bound hc (Nat.cast_nonneg N) (hM w hw) hr4 hm2 (hra w hw) (hμb w hw)
        (hM1 w hw) (hM2 w hw))
    (fun p _ => by
      have h1 : (0:ℝ) ≤ (if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3
          else (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3) := by
        split_ifs <;> positivity
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc 3)) (by linarith))
    hcount
  have hterm : ∀ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
      C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
        (4 * c ^ 3 * ((if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3
          else (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3) + 1))
      = 4 * c ^ 3 * C * ((if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then
            (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
          else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) +
          ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
    intro p _
    have h4 : (4:ℝ) ^ p.1 ≠ 0 := by positivity
    have h43 : ((4:ℝ) ^ p.1) ^ 3 ≠ 0 := by positivity
    have h2 : (2:ℝ) ^ p.2 ≠ 0 := by positivity
    have h23 : ((2:ℝ) ^ p.2) ^ 3 ≠ 0 := by positivity
    split_ifs
    · have e : ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 * ((N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3)
          = (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1 := by
        rw [mul_div_assoc', div_eq_div_iff h43 h4]
        ring
      calc C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
            (4 * c ^ 3 * ((N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3 + 1))
          = 4 * c ^ 3 * C * (((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
              ((N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3) + ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
            ring
        _ = 4 * c ^ 3 * C * ((N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1 +
              ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
            rw [e]
    · have e : ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 * ((N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3)
          = (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 := by
        rw [mul_div_assoc', div_eq_div_iff h23 h2]
        ring
      calc C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
            (4 * c ^ 3 * ((N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3 + 1))
          = 4 * c ^ 3 * C * (((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
              ((N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3) + ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
            ring
        _ = 4 * c ^ 3 * C * ((N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 +
              ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
            rw [e]
  have hg : ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
      (if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
        else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) ≤ 48 * (N:ℝ) ^ 6 := by
    calc ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
          (if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
            else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2)
        ≤ ∑ p ∈ dyCells X,
          (if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
            else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p _ _
          split_ifs <;> positivity
      _ = ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1),
            (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1 +
          ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => ¬ ((N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1)),
            (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2 := sum_ite _ _
      _ ≤ 32 * (N:ℝ) ^ 6 + 16 * (N:ℝ) ^ 6 := add_le_add (cells_A X N hX) (cells_B X N hX)
      _ = 48 * (N:ℝ) ^ 6 := by ring
  have hk : 0 ≤ 4 * c ^ 3 * C := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc 3)) hC
  calc ∑ w ∈ W, M w ^ 3
      ≤ ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
          C * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 *
          (4 * c ^ 3 * ((if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 / ((4:ℝ) ^ p.1) ^ 3
            else (N:ℝ) ^ 3 / ((2:ℝ) ^ p.2) ^ 3) + 1)) := hA
    _ = ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
          4 * c ^ 3 * C * ((if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then
              (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
            else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) +
            ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := sum_congr rfl hterm
    _ = 4 * c ^ 3 * C * (∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
          (if (N:ℝ) * 2 ^ p.2 ≤ 4 ^ p.1 then (N:ℝ) ^ 6 * ((2:ℝ) ^ p.2) ^ 2 / 4 ^ p.1
            else (N:ℝ) ^ 3 * ((4:ℝ) ^ p.1) ^ 2 / 2 ^ p.2) +
          ∑ p ∈ (dyCells X).filter (fun p : ℕ × ℕ => p.2 ≤ p.1 + 1),
            ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ 4 * c ^ 3 * C * (48 * (N:ℝ) ^ 6 + 65536 * (N:ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left (add_le_add hg (cells_C X N hX)) hk
    _ = 262336 * c ^ 3 * C * (N:ℝ) ^ 6 := by ring

/-! ### Sorting planes into cells -/

lemma dy_pow_log_floor_le (q : ℕ) {x : ℝ} (hx : 1 ≤ x) : (q:ℝ) ^ Nat.log q ⌊x⌋₊ ≤ x := by
  have h0 : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx).ne'
  calc (q:ℝ) ^ Nat.log q ⌊x⌋₊ = ((q ^ Nat.log q ⌊x⌋₊ : ℕ) : ℝ) := by rw [Nat.cast_pow]
    _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self q h0
    _ ≤ x := Nat.floor_le (by linarith)

lemma dy_lt_pow_log_floor_succ {q : ℕ} (hq : 1 < q) (x : ℝ) :
    x < (q:ℝ) ^ (Nat.log q ⌊x⌋₊ + 1) := by
  have h1 : ⌊x⌋₊ + 1 ≤ q ^ (Nat.log q ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self hq _
  have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (q:ℝ) ^ (Nat.log q ⌊x⌋₊ + 1) := by exact_mod_cast h1
  linarith [Nat.lt_floor_add_one x]

/-- The cell `(a, b)` of a plane with `1 ≤ |w| ≤ 3N²` and `μ₁² ≤ 2|w|` (Hermite) satisfies
`a ≤ log₂(2N)` and `b ≤ a + 1`. -/
lemma cell_facts {N : ℕ} {r μ : ℝ} {a b : ℕ}
    (ha1 : (4:ℝ) ^ a ≤ r) (ha2 : r < 4 ^ (a + 1)) (hb1 : (2:ℝ) ^ b ≤ μ)
    (hr2 : r ≤ 3 * N ^ 2) (hμ2 : μ ^ 2 ≤ 2 * r) :
    a ≤ Nat.log 2 (2 * N) ∧ b ≤ a + 1 := by
  constructor
  · apply Nat.le_log_of_pow_le (by norm_num)
    have h5 : ((2:ℝ) ^ a) ^ 2 ≤ 3 * (N:ℝ) ^ 2 := by
      rw [← dy_four_pow a]
      linarith
    have h6 : (2:ℝ) ^ a ≤ 2 * N := by
      by_contra hcon
      have hlt : 2 * (N:ℝ) < 2 ^ a := not_le.mp hcon
      have hN0 : (0:ℝ) ≤ 2 * N := by positivity
      have h7 : (2 * (N:ℝ)) ^ 2 < ((2:ℝ) ^ a) ^ 2 := pow_lt_pow_left₀ hlt hN0 (by norm_num)
      have h8 : (0:ℝ) ≤ (N:ℝ) ^ 2 := by positivity
      linarith
    exact_mod_cast h6
  · by_contra hcon
    have hlt : a + 1 < b := not_le.mp hcon
    have h7 : (2:ℝ) ^ (a + 2) ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) (by omega)
    have h8 : ((2:ℝ) ^ (a + 2)) ^ 2 ≤ μ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (le_trans h7 hb1) 2
    have h9 : ((2:ℝ) ^ (a + 2)) ^ 2 = 16 * 4 ^ a := by
      rw [dy_four_pow a]
      ring
    have h10 : (4:ℝ) ^ (a + 1) = 4 * 4 ^ a := by ring
    have h11 : (0:ℝ) < 4 ^ a := by positivity
    linarith

/-! ### Steps 1–6 combined -/

set_option maxHeartbeats 1000000 in
/-- **Theorem 4.1, assuming the geometric lemmas.** Planes are indexed by a type `ι`;
`Wadm` are the admissible planes and `Wnon` the non-admissible planes with `|w| ≤ 3N²`
other than the three coordinate planes. For a plane `w`: `r w = |w|`, `μ w = μ₁(w)`,
`L w = L_P`, `par w = par_P` and `M w = M_w`. `S = S₃(N)`, `A3 = N³ A(N)`, and
`Main = ½ ∑_{|w| ≤ 3N²} M_w³`.

The hypotheses are: the identity of Step 1 (`hS`); Proposition 3.7 (`hA3`); the size of
`|w|`, `μ₁ ≥ 1` and Hermite's inequality `μ₁² ≤ 2|w|`; the single-plane estimates of
Steps 2, 3 and 5 with a constant `c`; Lemma 5.2 with a constant `C`; the split of Step 5
(`hsplit`); and the main-term estimate of Step 6 from Lemma 5.4 (`hmain`). -/
theorem main_bound {ι : Type*} (Wadm Wnon : Finset ι) (N : ℕ) (hN : 1 ≤ N)
    (L par M r μ : ι → ℝ) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (S A3 Main J ζ3 : ℝ)
    (hS : S = A3 + ∑ w ∈ Wadm, (L w ^ 3 - L w * par w))
    (hA3 : |A3| ≤ c * (N:ℝ) ^ 6)
    (hrA : ∀ w ∈ Wadm, 1 ≤ r w ∧ r w ≤ 3 * (N:ℝ) ^ 2)
    (hμA : ∀ w ∈ Wadm, 1 ≤ μ w ∧ μ w ^ 2 ≤ 2 * r w ∧ r w ≤ 2 * N * μ w)
    (hLA : ∀ w ∈ Wadm, 0 ≤ L w ∧ 0 ≤ M w ∧ |L w - M w| ≤ c * N / μ w ∧
      M w ≤ c * (N:ℝ) ^ 2 / r w ∧ 0 ≤ par w ∧ par w ≤ c * L w * N / μ w)
    (hrN : ∀ w ∈ Wnon, 1 ≤ r w ∧ r w ≤ 3 * (N:ℝ) ^ 2)
    (hμN : ∀ w ∈ Wnon, 1 ≤ μ w ∧ μ w ^ 2 ≤ 2 * r w)
    (hMN : ∀ w ∈ Wnon, 0 ≤ M w ∧ M w ≤ c * (N:ℝ) ^ 2 / r w ∧ M w ≤ c * (N / μ w + 1))
    (hcA : ∀ R t : ℝ, 1 ≤ t → t ≤ R →
      ((Wadm.filter (fun w => r w ≤ R ∧ μ w ≤ t)).card : ℝ) ≤ C * R ^ 2 * t ^ 2)
    (hcN : ∀ R t : ℝ, 1 ≤ t → t ≤ R →
      ((Wnon.filter (fun w => r w ≤ R ∧ μ w ≤ t)).card : ℝ) ≤ C * R ^ 2 * t ^ 2)
    (hsplit : ∑ w ∈ Wadm, M w ^ 3 = Main - 3 * (N:ℝ) ^ 6 - ∑ w ∈ Wnon, M w ^ 3)
    (hmain : |Main - J / ζ3 * (N:ℝ) ^ 6 * Real.log N| ≤ c * (N:ℝ) ^ 6) :
    |S - J / ζ3 * (N:ℝ) ^ 6 * Real.log N| ≤ (2 * c + 3 + 17000000 * c ^ 3 * C) * (N:ℝ) ^ 6 := by
  have hX : (2:ℝ) ^ Nat.log 2 (2 * N) ≤ 2 * N := by
    have h := Nat.pow_log_le_self 2 (show 2 * N ≠ 0 by omega)
    exact_mod_cast h
  -- every plane lies in the dyadic cell given by `Nat.log`
  have hdy : ∀ w, 1 ≤ r w → 1 ≤ μ w →
      (4:ℝ) ^ Nat.log 4 ⌊r w⌋₊ ≤ r w ∧ r w < 4 ^ (Nat.log 4 ⌊r w⌋₊ + 1) ∧
      (2:ℝ) ^ Nat.log 2 ⌊μ w⌋₊ ≤ μ w ∧ μ w < 2 ^ (Nat.log 2 ⌊μ w⌋₊ + 1) := by
    intro w hr hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact_mod_cast dy_pow_log_floor_le 4 hr
    · exact_mod_cast dy_lt_pow_log_floor_succ (q := 4) (by norm_num) (r w)
    · exact_mod_cast dy_pow_log_floor_le 2 hm
    · exact_mod_cast dy_lt_pow_log_floor_succ (q := 2) (by norm_num) (μ w)
  -- Lemma 5.2 gives the number of planes in each cell
  have hcell : ∀ W : Finset ι, (∀ w ∈ W, 1 ≤ r w ∧ 1 ≤ μ w) →
      (∀ R t : ℝ, 1 ≤ t → t ≤ R →
        ((W.filter (fun w => r w ≤ R ∧ μ w ≤ t)).card : ℝ) ≤ C * R ^ 2 * t ^ 2) →
      ∀ p : ℕ × ℕ, p.2 ≤ p.1 + 1 →
        ((W.filter (fun w => (Nat.log 4 ⌊r w⌋₊, Nat.log 2 ⌊μ w⌋₊) = p)).card : ℝ) ≤
          (64 * C) * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 := by
    intro W hW hcW p hp
    have hsub : W.filter (fun w => (Nat.log 4 ⌊r w⌋₊, Nat.log 2 ⌊μ w⌋₊) = p) ⊆
        W.filter (fun w => r w ≤ 4 ^ (p.1 + 1) ∧ μ w ≤ 2 ^ (p.2 + 1)) := by
      intro w hw
      rw [mem_filter] at hw ⊢
      obtain ⟨hwW, hab⟩ := hw
      have hd := hdy w (hW w hwW).1 (hW w hwW).2
      have ha : Nat.log 4 ⌊r w⌋₊ = p.1 := by rw [← hab]
      have hb : Nat.log 2 ⌊μ w⌋₊ = p.2 := by rw [← hab]
      refine ⟨hwW, ?_, ?_⟩
      · rw [← ha]
        exact hd.2.1.le
      · rw [← hb]
        exact hd.2.2.2.le
    have hcard : ((W.filter (fun w => (Nat.log 4 ⌊r w⌋₊, Nat.log 2 ⌊μ w⌋₊) = p)).card : ℝ) ≤
        ((W.filter (fun w => r w ≤ 4 ^ (p.1 + 1) ∧ μ w ≤ 2 ^ (p.2 + 1))).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have ht1 : (1:ℝ) ≤ 2 ^ (p.2 + 1) := one_le_pow₀ (by norm_num)
    have htR : (2:ℝ) ^ (p.2 + 1) ≤ 4 ^ (p.1 + 1) := by
      calc (2:ℝ) ^ (p.2 + 1) ≤ 2 ^ (2 * (p.1 + 1)) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4 ^ (p.1 + 1) := by
            rw [pow_mul]
            norm_num
    calc ((W.filter (fun w => (Nat.log 4 ⌊r w⌋₊, Nat.log 2 ⌊μ w⌋₊) = p)).card : ℝ)
        ≤ ((W.filter (fun w => r w ≤ 4 ^ (p.1 + 1) ∧ μ w ≤ 2 ^ (p.2 + 1))).card : ℝ) := hcard
      _ ≤ C * ((4:ℝ) ^ (p.1 + 1)) ^ 2 * ((2:ℝ) ^ (p.2 + 1)) ^ 2 := hcW _ _ ht1 htR
      _ = (64 * C) * ((4:ℝ) ^ p.1) ^ 2 * ((2:ℝ) ^ p.2) ^ 2 := by ring
  -- facts about the cells of the admissible planes
  have factsA : ∀ w ∈ Wadm,
      (4:ℝ) ^ Nat.log 4 ⌊r w⌋₊ ≤ r w ∧ (2:ℝ) ^ Nat.log 2 ⌊μ w⌋₊ ≤ μ w ∧
      Nat.log 4 ⌊r w⌋₊ ≤ Nat.log 2 (2 * N) ∧ Nat.log 2 ⌊μ w⌋₊ ≤ Nat.log 4 ⌊r w⌋₊ + 1 ∧
      (4:ℝ) ^ Nat.log 4 ⌊r w⌋₊ ≤ 4 * N * 2 ^ Nat.log 2 ⌊μ w⌋₊ := by
    intro w hw
    obtain ⟨hr1, hr2⟩ := hrA w hw
    obtain ⟨hμ1, hμ2, hrμ⟩ := hμA w hw
    obtain ⟨d1, d2, d3, d4⟩ := hdy w hr1 hμ1
    obtain ⟨e1, e2⟩ := cell_facts d1 d2 d3 hr2 hμ2
    refine ⟨d1, d3, e1, e2, ?_⟩
    have h1 : 2 * (N:ℝ) * μ w ≤ 2 * N * 2 ^ (Nat.log 2 ⌊μ w⌋₊ + 1) :=
      mul_le_mul_of_nonneg_left d4.le (by positivity)
    have h2 : 2 * (N:ℝ) * 2 ^ (Nat.log 2 ⌊μ w⌋₊ + 1) = 4 * N * 2 ^ Nat.log 2 ⌊μ w⌋₊ := by
      ring
    linarith
  -- facts about the cells of the other non-admissible planes
  have factsN : ∀ w ∈ Wnon,
      (4:ℝ) ^ Nat.log 4 ⌊r w⌋₊ ≤ r w ∧ (2:ℝ) ^ Nat.log 2 ⌊μ w⌋₊ ≤ μ w ∧
      Nat.log 4 ⌊r w⌋₊ ≤ Nat.log 2 (2 * N) ∧ Nat.log 2 ⌊μ w⌋₊ ≤ Nat.log 4 ⌊r w⌋₊ + 1 := by
    intro w hw
    obtain ⟨hr1, hr2⟩ := hrN w hw
    obtain ⟨hμ1, hμ2⟩ := hμN w hw
    obtain ⟨d1, d2, d3, _⟩ := hdy w hr1 hμ1
    obtain ⟨e1, e2⟩ := cell_facts d1 d2 d3 hr2 hμ2
    exact ⟨d1, d3, e1, e2⟩
  have h64 : (0:ℝ) ≤ 64 * C := by linarith
  -- Step 4
  have h4 := step4_bound Wadm hX hc h64 L M par r μ
    (fun w => Nat.log 4 ⌊r w⌋₊) (fun w => Nat.log 2 ⌊μ w⌋₊)
    (fun w hw => (hLA w hw).1) (fun w hw => (hLA w hw).2.1)
    (fun w hw => (hLA w hw).2.2.1) (fun w hw => (hLA w hw).2.2.2.2.1)
    (fun w hw => (hLA w hw).2.2.2.2.2) (fun w hw => (hLA w hw).2.2.2.1)
    (fun w hw => (factsA w hw).1) (fun w hw => (factsA w hw).2.1)
    (fun w hw => (factsA w hw).2.2.1) (fun w hw => (factsA w hw).2.2.2.1)
    (fun w hw => (factsA w hw).2.2.2.2)
    (fun p hp => hcell Wadm (fun w hw => ⟨(hrA w hw).1, (hμA w hw).1⟩) hcA p
      (mem_filter.mp hp).2.1)
  -- Step 5
  have h5 := step5_bound Wnon hX hc h64 M r μ
    (fun w => Nat.log 4 ⌊r w⌋₊) (fun w => Nat.log 2 ⌊μ w⌋₊)
    (fun w hw => (hMN w hw).1) (fun w hw => (hMN w hw).2.1) (fun w hw => (hMN w hw).2.2)
    (fun w hw => (factsN w hw).1) (fun w hw => (factsN w hw).2.1)
    (fun w hw => (factsN w hw).2.2.1) (fun w hw => (factsN w hw).2.2.2)
    (fun p hp => hcell Wnon (fun w hw => ⟨(hrN w hw).1, (hμN w hw).1⟩) hcN p
      (mem_filter.mp hp).2)
  -- combine
  have hD : |∑ w ∈ Wadm, ((L w ^ 3 - L w * par w) - M w ^ 3)| ≤
      2176 * c ^ 3 * (64 * C) * (N:ℝ) ^ 6 :=
    le_trans (abs_sum_le_sum_abs _ _) h4
  have hsum : ∑ w ∈ Wadm, (L w ^ 3 - L w * par w) =
      ∑ w ∈ Wadm, M w ^ 3 + ∑ w ∈ Wadm, ((L w ^ 3 - L w * par w) - M w ^ 3) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    ring
  have hnon0 : 0 ≤ ∑ w ∈ Wnon, M w ^ 3 := sum_nonneg (fun w hw => pow_nonneg (hMN w hw).1 3)
  have hN6 : (0:ℝ) ≤ (N:ℝ) ^ 6 := by positivity
  have hk : 0 ≤ c ^ 3 * C * (N:ℝ) ^ 6 := mul_nonneg (mul_nonneg (pow_nonneg hc 3) hC) hN6
  have hcN6 : 0 ≤ c * (N:ℝ) ^ 6 := mul_nonneg hc hN6
  have key : S - J / ζ3 * (N:ℝ) ^ 6 * Real.log N =
      A3 + (Main - J / ζ3 * (N:ℝ) ^ 6 * Real.log N) - 3 * (N:ℝ) ^ 6 - ∑ w ∈ Wnon, M w ^ 3 +
        ∑ w ∈ Wadm, ((L w ^ 3 - L w * par w) - M w ^ 3) := by
    rw [hS, hsum, hsplit]
    ring
  rw [key, abs_le]
  obtain ⟨e1, e2⟩ := abs_le.mp hA3
  obtain ⟨e3, e4⟩ := abs_le.mp hmain
  obtain ⟨e5, e6⟩ := abs_le.mp hD
  constructor <;> linarith [e1, e2, e3, e4, e5, e6, hnon0, h5, hk, hN6, hcN6]

end SingularMatrices
