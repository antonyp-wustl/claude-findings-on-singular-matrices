import SingularMatrices.SmallN

/-!
# The exact decomposition for 3×3 matrices (Section 3), part 1

* `det3_eq_dot_cross`: the determinant is the triple product `(r × s) · t`.
* `S3_eq_sum_Lw`: `S₃(N) = ∑_{(r,s)} L(r × s)`, where `L(n)` counts the rows orthogonal to `n`.
  This is the formula behind the first algorithm of Section 6.1.
* `S3_split`: **Lemma 3.1** in pair form. Parallel pairs contribute `N³` each; every other
  pair contributes the number of rows in the plane it spans.
* `cross3_eq_zero_iff_dir3`: two rows are parallel iff they have the same direction.
* `A3count_eq_sum_prim`, `A3count_eq_sum_g`: the first identity of **Lemma 3.2**,
  `A(N) = ∑_{m ≤ N} g(m) ⌊N/m⌋²`, where `g(m)` counts the primitive rows with largest entry `m`.

Still to do: grouping the non-parallel pairs by plane (`∑_P L_P I_P`), Lemma 3.3, Proposition 3.5,
the Möbius formula for `g(m)`, and Theorem 3.6.
-/

namespace SingularMatrices

open Finset

/-! ### Cross and dot products -/

/-- The cross product of two rows, as an integer vector. -/
def cross3 (r s : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ :=
  ((r.2.1 : ℤ) * s.2.2 - (r.2.2 : ℤ) * s.2.1,
   (r.2.2 : ℤ) * s.1 - (r.1 : ℤ) * s.2.2,
   (r.1 : ℤ) * s.2.1 - (r.2.1 : ℤ) * s.1)

/-- The dot product of an integer vector with a row. -/
def dot3 (n : ℤ × ℤ × ℤ) (t : ℕ × ℕ × ℕ) : ℤ :=
  n.1 * t.1 + n.2.1 * t.2.1 + n.2.2 * t.2.2

/-- The determinant is the triple product. -/
lemma det3_eq_dot_cross (r s t : ℕ × ℕ × ℕ) : det3 r s t = dot3 (cross3 r s) t := by
  simp only [det3, dot3, cross3]
  ring

/-- `r × s = 0` in terms of natural numbers. -/
lemma cross3_eq_zero_iff_nat (r s : ℕ × ℕ × ℕ) :
    cross3 r s = 0 ↔ (r.2.1 * s.2.2 = r.2.2 * s.2.1 ∧ r.2.2 * s.1 = r.1 * s.2.2 ∧
      r.1 * s.2.1 = r.2.1 * s.1) := by
  simp only [cross3, Prod.mk_eq_zero, sub_eq_zero]
  constructor <;> intro h <;> exact_mod_cast h

/-- The number of rows orthogonal to `n`; for `n ≠ 0`, the number of rows on the plane `n^⊥`. -/
def Lw (N : ℕ) (n : ℤ × ℤ × ℤ) : ℕ := ((rows3 N).filter (fun t => dot3 n t = 0)).card

lemma card_rows3 (N : ℕ) : (rows3 N).card = N ^ 3 := by
  simp only [rows3, entries, card_product, Nat.card_Icc, Nat.add_sub_cancel]
  ring

lemma Lw_zero (N : ℕ) : Lw N 0 = N ^ 3 := by
  have h : (rows3 N).filter (fun t => dot3 0 t = 0) = rows3 N := by
    apply filter_true_of_mem
    intro t _
    simp [dot3]
  rw [Lw, h, card_rows3]

/-! ### Lemma 3.1 -/

/-- `S₃(N) = ∑_{(r,s)} L(r × s)`: fix the first two rows and count the third. -/
theorem S3_eq_sum_Lw (N : ℕ) :
    S3 N = ∑ x ∈ rows3 N ×ˢ rows3 N, Lw N (cross3 x.1 x.2) := by
  rw [S3, card_filter, sum_product (rows3 N) (rows3 N ×ˢ rows3 N),
    sum_product (rows3 N) (rows3 N)]
  apply sum_congr rfl
  intro r _
  rw [sum_product (rows3 N) (rows3 N)]
  apply sum_congr rfl
  intro s _
  rw [Lw, card_filter]
  apply sum_congr rfl
  intro t _
  simp only [det3_eq_dot_cross]

/-- The number `A(N)` of ordered pairs of parallel rows. -/
def A3count (N : ℕ) : ℕ := ((rows3 N ×ˢ rows3 N).filter (fun x => cross3 x.1 x.2 = 0)).card

/-- **Lemma 3.1**, pair form: `S₃(N) = N³ A(N) + ∑_{(r,s) not parallel} L(r × s)`. -/
theorem S3_split (N : ℕ) :
    S3 N = N ^ 3 * A3count N +
      ∑ x ∈ (rows3 N ×ˢ rows3 N).filter (fun x => ¬ cross3 x.1 x.2 = 0),
        Lw N (cross3 x.1 x.2) := by
  rw [S3_eq_sum_Lw, ← sum_filter_add_sum_filter_not (rows3 N ×ˢ rows3 N)
    (fun x => cross3 x.1 x.2 = 0)]
  congr 1
  have h : ∀ x ∈ (rows3 N ×ˢ rows3 N).filter (fun x => cross3 x.1 x.2 = 0),
      Lw N (cross3 x.1 x.2) = N ^ 3 := by
    intro x hx
    rw [(mem_filter.mp hx).2, Lw_zero]
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm, A3count]

/-! ### Directions of rows -/

/-- The gcd of the three entries of a row. -/
def gcd3 (v : ℕ × ℕ × ℕ) : ℕ := Nat.gcd v.1 (Nat.gcd v.2.1 v.2.2)

/-- The direction of a row: divide out the gcd of its entries. -/
def dir3 (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (v.1 / gcd3 v, v.2.1 / gcd3 v, v.2.2 / gcd3 v)

/-- The primitive rows in the box, i.e. the possible directions. -/
def prim3 (N : ℕ) : Finset (ℕ × ℕ × ℕ) := (rows3 N).filter (fun v => gcd3 v = 1)

/-- The largest entry of a row. -/
def max3 (v : ℕ × ℕ × ℕ) : ℕ := max v.1 (max v.2.1 v.2.2)

lemma gcd3_pos {v : ℕ × ℕ × ℕ} (h : 0 < v.1) : 0 < gcd3 v := Nat.gcd_pos_of_pos_left _ h

lemma gcd3_dvd (v : ℕ × ℕ × ℕ) : gcd3 v ∣ v.1 ∧ gcd3 v ∣ v.2.1 ∧ gcd3 v ∣ v.2.2 :=
  ⟨Nat.gcd_dvd_left _ _, (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _),
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)⟩

lemma gcd3_dir3 {v : ℕ × ℕ × ℕ} (h : 0 < v.1) : gcd3 (dir3 v) = 1 := by
  obtain ⟨h1, h2, h3⟩ := gcd3_dvd v
  have hg := gcd3_pos h
  have h23 : gcd3 v ∣ Nat.gcd v.2.1 v.2.2 := Nat.dvd_gcd h2 h3
  show Nat.gcd (v.1 / gcd3 v) (Nat.gcd (v.2.1 / gcd3 v) (v.2.2 / gcd3 v)) = 1
  rw [Nat.gcd_div h2 h3, Nat.gcd_div h1 h23]
  exact Nat.div_self hg

lemma mul_max3 (k : ℕ) (v : ℕ × ℕ × ℕ) :
    k * max3 v = max (k * v.1) (max (k * v.2.1) (k * v.2.2)) := by
  simp only [max3]
  rw [Nat.mul_max_mul_left, Nat.mul_max_mul_left]

/-- Two primitive vectors with positive first entries that are parallel are equal. -/
lemma prim_eq_of_parallel {p₁ p₂ p₃ q₁ q₂ q₃ : ℕ} (hp1 : 0 < p₁)
    (hp : Nat.gcd p₁ (Nat.gcd p₂ p₃) = 1) (hq : Nat.gcd q₁ (Nat.gcd q₂ q₃) = 1)
    (h2 : p₁ * q₂ = p₂ * q₁) (h3 : p₁ * q₃ = p₃ * q₁) :
    p₁ = q₁ ∧ p₂ = q₂ ∧ p₃ = q₃ := by
  have hpq : p₁ ∣ q₁ := by
    have e : Nat.gcd (q₁ * p₁) (Nat.gcd (q₁ * p₂) (q₁ * p₃)) = q₁ := by
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hp, mul_one]
    rw [← e]
    exact Nat.dvd_gcd (dvd_mul_left _ _)
      (Nat.dvd_gcd (Dvd.intro q₂ (h2.trans (mul_comm p₂ q₁)))
        (Dvd.intro q₃ (h3.trans (mul_comm p₃ q₁))))
  have hqp : q₁ ∣ p₁ := by
    have e : Nat.gcd (p₁ * q₁) (Nat.gcd (p₁ * q₂) (p₁ * q₃)) = p₁ := by
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hq, mul_one]
    rw [← e]
    exact Nat.dvd_gcd (dvd_mul_left _ _)
      (Nat.dvd_gcd (Dvd.intro p₂ ((mul_comm q₁ p₂).trans h2.symm))
        (Dvd.intro p₃ ((mul_comm q₁ p₃).trans h3.symm)))
  have h11 : p₁ = q₁ := Nat.dvd_antisymm hpq hqp
  refine ⟨h11, ?_, ?_⟩
  · have e : p₁ * q₂ = p₁ * p₂ := by
      rw [h2, ← h11, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hp1 e).symm
  · have e : p₁ * q₃ = p₁ * p₃ := by
      rw [h3, ← h11, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hp1 e).symm

/-- The arithmetic core: with `r = g p`, `s = h q`, and `p`, `q` primitive, the rows `r` and
`s` are parallel iff `p = q`. -/
lemma parallel_iff_aux {p₁ p₂ p₃ q₁ q₂ q₃ g h : ℕ} (hg : 0 < g) (hh : 0 < h) (hp1 : 0 < p₁)
    (hp : Nat.gcd p₁ (Nat.gcd p₂ p₃) = 1) (hq : Nat.gcd q₁ (Nat.gcd q₂ q₃) = 1) :
    ((p₂ * g) * (q₃ * h) = (p₃ * g) * (q₂ * h) ∧ (p₃ * g) * (q₁ * h) = (p₁ * g) * (q₃ * h) ∧
      (p₁ * g) * (q₂ * h) = (p₂ * g) * (q₁ * h)) ↔ (p₁ = q₁ ∧ p₂ = q₂ ∧ p₃ = q₃) := by
  have hgh : 0 < g * h := Nat.mul_pos hg hh
  have canc : ∀ a b c d : ℕ, (a * g) * (b * h) = (c * g) * (d * h) ↔ a * b = c * d := by
    intro a b c d
    constructor
    · intro e
      apply Nat.eq_of_mul_eq_mul_right hgh
      calc a * b * (g * h) = (a * g) * (b * h) := by ring
        _ = (c * g) * (d * h) := e
        _ = c * d * (g * h) := by ring
    · intro e
      calc (a * g) * (b * h) = a * b * (g * h) := by ring
        _ = c * d * (g * h) := by rw [e]
        _ = (c * g) * (d * h) := by ring
  rw [canc, canc, canc]
  constructor
  · rintro ⟨_, e2, e3⟩
    exact prim_eq_of_parallel hp1 hp hq e3 e2.symm
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨mul_comm _ _, mul_comm _ _, mul_comm _ _⟩

/-- Two rows with positive first entries are parallel iff they have the same direction. -/
lemma cross3_eq_zero_iff_dir3 {r s : ℕ × ℕ × ℕ} (hr : 0 < r.1) (hs : 0 < s.1) :
    cross3 r s = 0 ↔ dir3 r = dir3 s := by
  obtain ⟨gr1, gr2, gr3⟩ := gcd3_dvd r
  obtain ⟨gs1, gs2, gs3⟩ := gcd3_dvd s
  have key := parallel_iff_aux (p₁ := r.1 / gcd3 r) (p₂ := r.2.1 / gcd3 r)
    (p₃ := r.2.2 / gcd3 r) (q₁ := s.1 / gcd3 s) (q₂ := s.2.1 / gcd3 s) (q₃ := s.2.2 / gcd3 s)
    (gcd3_pos hr) (gcd3_pos hs) (Nat.div_pos (Nat.le_of_dvd hr gr1) (gcd3_pos hr))
    (gcd3_dir3 hr) (gcd3_dir3 hs)
  rw [Nat.div_mul_cancel gr1, Nat.div_mul_cancel gr2, Nat.div_mul_cancel gr3,
    Nat.div_mul_cancel gs1, Nat.div_mul_cancel gs2, Nat.div_mul_cancel gs3] at key
  rw [cross3_eq_zero_iff_nat, key]
  simp only [dir3, Prod.mk.injEq]

/-! ### Lemma 3.2: counting parallel pairs -/

/-- Every row has its direction among the primitive rows in the box. -/
lemma dir3_mem_prim3 {N : ℕ} {v : ℕ × ℕ × ℕ} (hv : v ∈ rows3 N) : dir3 v ∈ prim3 N := by
  obtain ⟨a, b, c⟩ := v
  simp only [rows3, entries, mem_product, mem_Icc] at hv
  obtain ⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩, ⟨hc1, hcN⟩⟩ := hv
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hg : 0 < gcd3 (a, b, c) := gcd3_pos (v := (a, b, c)) ha
  obtain ⟨g1, g2, g3⟩ := gcd3_dvd (a, b, c)
  have hprim := gcd3_dir3 (v := (a, b, c)) ha
  simp only [prim3, rows3, entries, dir3, mem_filter, mem_product, mem_Icc]
  refine ⟨⟨⟨Nat.div_pos (Nat.le_of_dvd ha g1) hg, le_trans (Nat.div_le_self _ _) haN⟩,
    ⟨Nat.div_pos (Nat.le_of_dvd hb g2) hg, le_trans (Nat.div_le_self _ _) hbN⟩,
    ⟨Nat.div_pos (Nat.le_of_dvd hc g3) hg, le_trans (Nat.div_le_self _ _) hcN⟩⟩, hprim⟩

/-- The direction `p` contains exactly `⌊N / max p⌋` rows, namely `k • p` for
`1 ≤ k ≤ ⌊N / max p⌋`. -/
lemma fiber3_card {N : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ prim3 N) :
    ((rows3 N).filter (fun x => dir3 x = p)).card = N / max3 p := by
  obtain ⟨p1, p2, p3⟩ := p
  simp only [prim3, rows3, entries, mem_filter, mem_product, mem_Icc] at hp
  obtain ⟨⟨⟨hp1, _⟩, ⟨hp2, _⟩, ⟨hp3, _⟩⟩, hprim⟩ := hp
  have hprim' : Nat.gcd p1 (Nat.gcd p2 p3) = 1 := hprim
  have hm : 0 < max3 (p1, p2, p3) :=
    lt_of_lt_of_le (by omega : 0 < p1) (le_max_left p1 (max p2 p3))
  have hinj : Function.Injective (fun k : ℕ => (k * p1, k * p2, k * p3)) := by
    intro k l hkl
    simp only [Prod.mk.injEq] at hkl
    exact Nat.eq_of_mul_eq_mul_right (by omega) hkl.1
  have hset : (rows3 N).filter (fun x => dir3 x = (p1, p2, p3)) =
      (Icc 1 (N / max3 (p1, p2, p3))).image (fun k => (k * p1, k * p2, k * p3)) := by
    ext ⟨a, b, c⟩
    simp only [rows3, entries, dir3, mem_filter, mem_product, mem_Icc, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩, ⟨hc1, hcN⟩⟩, e1, e2, e3⟩
      obtain ⟨g1, g2, g3⟩ := gcd3_dvd (a, b, c)
      have hg : 0 < gcd3 (a, b, c) := gcd3_pos (v := (a, b, c)) (by show 0 < a; omega)
      have ea : gcd3 (a, b, c) * p1 = a := by
        rw [← e1]
        exact Nat.mul_div_cancel' g1
      have eb : gcd3 (a, b, c) * p2 = b := by
        rw [← e2]
        exact Nat.mul_div_cancel' g2
      have ec : gcd3 (a, b, c) * p3 = c := by
        rw [← e3]
        exact Nat.mul_div_cancel' g3
      refine ⟨gcd3 (a, b, c), ⟨hg, ?_⟩, ea, eb, ec⟩
      rw [Nat.le_div_iff_mul_le hm, mul_max3]
      simp only [ea, eb, ec]
      exact max_le haN (max_le hbN hcN)
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl, rfl, rfl⟩
      have hk : 0 < k := by omega
      have hkm : k * max3 (p1, p2, p3) ≤ N := (Nat.le_div_iff_mul_le hm).mp hkN
      rw [mul_max3] at hkm
      have h1 : k * p1 ≤ N := le_trans (le_max_left _ _) hkm
      have h2 : k * p2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkm
      have h3 : k * p3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkm
      have hgcd : gcd3 (k * p1, k * p2, k * p3) = k := by
        show Nat.gcd (k * p1) (Nat.gcd (k * p2) (k * p3)) = k
        rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hprim', mul_one]
      refine ⟨⟨⟨Nat.mul_pos hk (by omega), h1⟩, ⟨Nat.mul_pos hk (by omega), h2⟩,
        ⟨Nat.mul_pos hk (by omega), h3⟩⟩, ?_, ?_, ?_⟩
      · rw [hgcd, Nat.mul_div_cancel_left p1 hk]
      · rw [hgcd, Nat.mul_div_cancel_left p2 hk]
      · rw [hgcd, Nat.mul_div_cancel_left p3 hk]
  rw [hset, card_image_of_injective _ hinj, Nat.card_Icc, Nat.add_sub_cancel]

/-- `A(N) = ∑_{p primitive} ⌊N / max p⌋²`. -/
theorem A3count_eq_sum_prim (N : ℕ) : A3count N = ∑ v ∈ prim3 N, (N / max3 v) ^ 2 := by
  have h1 : (rows3 N ×ˢ rows3 N).filter (fun x => cross3 x.1 x.2 = 0) =
      (rows3 N ×ˢ rows3 N).filter (fun x => dir3 x.1 = dir3 x.2) := by
    apply filter_congr
    rintro ⟨r, s⟩ hx
    rw [mem_product] at hx
    have hr : 0 < r.1 := by
      have h := hx.1
      simp only [rows3, entries, mem_product, mem_Icc] at h
      omega
    have hs : 0 < s.1 := by
      have h := hx.2
      simp only [rows3, entries, mem_product, mem_Icc] at h
      omega
    exact cross3_eq_zero_iff_dir3 hr hs
  rw [A3count, h1, card_pairs_eq_sum_sq (s := rows3 N) (t := prim3 N) (f := dir3)
    (fun x hx => dir3_mem_prim3 hx)]
  apply sum_congr rfl
  intro p hp
  rw [fiber3_card hp]

/-- `g3 N m` counts the primitive rows in the box with largest entry `m`. -/
def g3 (N m : ℕ) : ℕ := ((prim3 N).filter (fun v => max3 v = m)).card

/-- **Lemma 3.2**, first identity: `A(N) = ∑_{m ≤ N} g(m) ⌊N/m⌋²`. -/
theorem A3count_eq_sum_g (N : ℕ) : A3count N = ∑ m ∈ Icc 1 N, g3 N m * (N / m) ^ 2 := by
  have hmaps : ∀ v ∈ prim3 N, max3 v ∈ Icc 1 N := by
    intro v hv
    obtain ⟨a, b, c⟩ := v
    simp only [prim3, rows3, entries, mem_filter, mem_product, mem_Icc] at hv
    obtain ⟨⟨⟨ha1, haN⟩, ⟨_, hbN⟩, ⟨_, hcN⟩⟩, _⟩ := hv
    rw [mem_Icc]
    exact ⟨le_trans ha1 (le_max_left a (max b c)), max_le haN (max_le hbN hcN)⟩
  rw [A3count_eq_sum_prim, ← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro m _
  have h : ∀ v ∈ (prim3 N).filter (fun v => max3 v = m), (N / max3 v) ^ 2 = (N / m) ^ 2 := by
    intro v hv
    rw [(mem_filter.mp hv).2]
  rw [sum_congr rfl h, sum_const, smul_eq_mul, g3]

-- Checks against the paper: the parallel-pair term `N³ A(N)` is 80 for `N = 2`
-- and 891 for `N = 3` (Appendix A data), so `A(2) = 10` and `A(3) = 33`.
example : A3count 2 = 10 := by native_decide
example : A3count 3 = 33 := by native_decide

end SingularMatrices
