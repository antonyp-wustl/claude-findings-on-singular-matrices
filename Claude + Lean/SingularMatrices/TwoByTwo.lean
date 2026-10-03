import Mathlib

/-!
# Singular 2×2 matrices with entries in `{1, …, N}`

This file formalizes Proposition 2.1 of the paper
*How Often Is a Random Integer Matrix Singular?*:

  `S₂(N) = 2 ∑_{m=1}^{N} φ(m) ⌊N/m⌋² − N²`,

where `S₂(N)` is the number of 2×2 matrices with entries in `{1, …, N}` and determinant `0`.

The proof follows the paper.
* A matrix with rows `(a, b)` and `(c, d)` is singular iff `a * d = b * c`, that is, iff its
  rows are parallel.
* Every row `(a, b)` is `k • (p, q)` for a unique coprime pair `(p, q)`, its *direction*
  (`dir`). Two rows are parallel iff they have the same direction (`mul_eq_mul_iff_dir_eq`).
* The direction `(p, q)` carries `⌊N / max p q⌋` rows (`fiber_card`). Hence
  `S₂(N) = ∑_{(p,q) coprime} ⌊N / max p q⌋²` (`S2_eq_sum_prim`).
* There are `φ(m)` coprime pairs with `q ≤ p = m`, and `φ(m)` with `p ≤ q = m`. Only `(1, 1)`
  is counted twice (`sum_primBelow`, `sum_primAbove`, `sum_primInter`).

The main results are `S2_add_sq` and `S2_formula`.
-/

namespace SingularMatrices

/-! ### Definitions -/

/-- The possible entries `{1, …, N}`. -/
abbrev entries (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The possible rows `{1, …, N}²` of a 2×2 matrix. -/
abbrev rows2 (N : ℕ) : Finset (ℕ × ℕ) := entries N ×ˢ entries N

/-- The number of singular 2×2 matrices with entries in `{1, …, N}`. A matrix is the pair of
its rows `((a, b), (c, d))`, and it is singular iff `a * d = b * c`. -/
def S2 (N : ℕ) : ℕ :=
  ((rows2 N ×ˢ rows2 N).filter (fun x => x.1.1 * x.2.2 = x.1.2 * x.2.1)).card

-- A check against the paper: there are 6 singular matrices for `N = 2`.
example : S2 2 = 6 := by decide

/-- The direction of a row: divide out the gcd. -/
def dir (v : ℕ × ℕ) : ℕ × ℕ := (v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2)

/-- The coprime pairs in the box, i.e. the possible directions. -/
def prim (N : ℕ) : Finset (ℕ × ℕ) := (rows2 N).filter (fun v => Nat.Coprime v.1 v.2)

/-- The square of the number of rows in the direction `v`. -/
def Fn (N : ℕ) (v : ℕ × ℕ) : ℕ := (N / max v.1 v.2) ^ 2

/-- Directions `(p, q)` with `q ≤ p`. -/
def primBelow (N : ℕ) : Finset (ℕ × ℕ) := (prim N).filter (fun v => v.2 ≤ v.1)

/-- Directions `(p, q)` with `p ≤ q`. -/
def primAbove (N : ℕ) : Finset (ℕ × ℕ) := (prim N).filter (fun v => v.1 ≤ v.2)

/-! ### Parallel rows have the same direction -/

/-- Two coprime pairs with `p * q' = q * p'` and `0 < p` are equal. -/
lemma eq_of_coprime_of_mul_eq {p q p' q' : ℕ} (hp : 0 < p)
    (h : Nat.Coprime p q) (h' : Nat.Coprime p' q') (hx : p * q' = q * p') :
    p = p' ∧ q = q' := by
  have h1 : p ∣ p' := by
    have hd : p ∣ q * p' := Dvd.intro q' hx
    exact h.dvd_of_dvd_mul_left hd
  have h2 : p' ∣ p := by
    have hd : p' ∣ p * q' := Dvd.intro q ((mul_comm p' q).trans hx.symm)
    exact h'.dvd_of_dvd_mul_right hd
  have hpp : p = p' := Nat.dvd_antisymm h1 h2
  refine ⟨hpp, ?_⟩
  rw [← hpp] at hx
  have h3 : p * q' = p * q := hx.trans (mul_comm q p)
  exact (Nat.eq_of_mul_eq_mul_left hp h3).symm

/-- The arithmetic core: if `a = p g`, `b = q g`, `c = p' h`, `d = q' h` with both pairs
coprime, then `a d = b c` iff `(p, q) = (p', q')`. -/
lemma cross_iff {p q p' q' g h : ℕ} (hg : 0 < g) (hh : 0 < h) (hp : 0 < p)
    (c1 : Nat.Coprime p q) (c2 : Nat.Coprime p' q') :
    (p * g) * (q' * h) = (q * g) * (p' * h) ↔ (p = p' ∧ q = q') := by
  constructor
  · intro hx
    have hx' : (p * q') * (g * h) = (q * p') * (g * h) := by
      calc (p * q') * (g * h) = (p * g) * (q' * h) := by ring
        _ = (q * g) * (p' * h) := hx
        _ = (q * p') * (g * h) := by ring
    exact eq_of_coprime_of_mul_eq hp c1 c2 (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg hh) hx')
  · rintro ⟨rfl, rfl⟩
    ring

/-- Two rows with positive first entries are parallel iff they have the same direction. -/
lemma mul_eq_mul_iff_dir_eq {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c) :
    a * d = b * c ↔ dir (a, b) = dir (c, d) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hh : 0 < Nat.gcd c d := Nat.gcd_pos_of_pos_left d hc
  have key := cross_iff (p := a / Nat.gcd a b) (q := b / Nat.gcd a b)
    (p' := c / Nat.gcd c d) (q' := d / Nat.gcd c d) hg hh
    (Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg)
    (Nat.coprime_div_gcd_div_gcd hg) (Nat.coprime_div_gcd_div_gcd hh)
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_left a b), Nat.div_mul_cancel (Nat.gcd_dvd_right a b),
    Nat.div_mul_cancel (Nat.gcd_dvd_left c d), Nat.div_mul_cancel (Nat.gcd_dvd_right c d)] at key
  rw [key]
  constructor
  · intro hx
    simpa [dir] using hx
  · intro hx
    simpa [dir] using hx

/-! ### Counting rows by direction -/

/-- Every row has its direction among the coprime pairs in the box. -/
lemma dir_mem_prim {N : ℕ} {v : ℕ × ℕ} (hv : v ∈ rows2 N) : dir v ∈ prim N := by
  obtain ⟨a, b⟩ := v
  simp only [rows2, entries, Finset.mem_product, Finset.mem_Icc] at hv
  obtain ⟨⟨ha1, haN⟩, hb1, hbN⟩ := hv
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  simp only [prim, rows2, entries, dir, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg,
      le_trans (Nat.div_le_self a _) haN⟩,
    Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg,
      le_trans (Nat.div_le_self b _) hbN⟩, Nat.coprime_div_gcd_div_gcd hg⟩

/-- The direction `(p, q)` contains exactly `⌊N / max p q⌋` rows, namely `k • (p, q)` for
`1 ≤ k ≤ ⌊N / max p q⌋`. -/
lemma fiber_card {N p q : ℕ} (hpq : (p, q) ∈ prim N) :
    ((rows2 N).filter (fun x => dir x = (p, q))).card = N / max p q := by
  simp only [prim, rows2, entries, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc] at hpq
  obtain ⟨⟨⟨hp1, _⟩, hq1, _⟩, hcop⟩ := hpq
  have hm : 0 < max p q := lt_of_lt_of_le (by omega : 0 < p) (le_max_left p q)
  have hinj : Function.Injective (fun k : ℕ => (k * p, k * q)) := by
    intro k l hkl
    simp only [Prod.mk.injEq] at hkl
    exact Nat.eq_of_mul_eq_mul_right (by omega) hkl.1
  have hset : (rows2 N).filter (fun x => dir x = (p, q)) =
      (Finset.Icc 1 (N / max p q)).image (fun k => (k * p, k * q)) := by
    ext ⟨a, b⟩
    simp only [rows2, entries, dir, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hpa, hqb⟩
      have ea : Nat.gcd a b * p = a := by
        rw [← hpa]
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
      have eb : Nat.gcd a b * q = b := by
        rw [← hqb]
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
      refine ⟨Nat.gcd a b, ⟨Nat.gcd_pos_of_pos_left b (by omega), ?_⟩, ea, eb⟩
      rw [Nat.le_div_iff_mul_le hm]
      rcases le_total p q with h | h
      · rw [max_eq_right h, eb]
        exact hbN
      · rw [max_eq_left h, ea]
        exact haN
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl, rfl⟩
      have hk : 0 < k := by omega
      have hkm : k * max p q ≤ N := (Nat.le_div_iff_mul_le hm).mp hkN
      have hkp : k * p ≤ N := le_trans (Nat.mul_le_mul le_rfl (le_max_left p q)) hkm
      have hkq : k * q ≤ N := le_trans (Nat.mul_le_mul le_rfl (le_max_right p q)) hkm
      have hgcd : Nat.gcd (k * p) (k * q) = k := by
        rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop, mul_one]
      refine ⟨⟨⟨Nat.mul_pos hk (by omega), hkp⟩, Nat.mul_pos hk (by omega), hkq⟩, ?_, ?_⟩
      · rw [hgcd, Nat.mul_div_cancel_left p hk]
      · rw [hgcd, Nat.mul_div_cancel_left q hk]
  rw [hset, Finset.card_image_of_injective _ hinj, Nat.card_Icc, Nat.add_sub_cancel]

/-- Counting pairs with equal labels: the number of pairs `(x, y)` in `s × s` with
`f x = f y` is the sum of the squares of the fibre sizes. -/
lemma card_pairs_eq_sum_sq {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hf : ∀ x ∈ s, f x ∈ t) :
    ((s ×ˢ s).filter (fun x => f x.1 = f x.2)).card =
      ∑ v ∈ t, ((s.filter (fun x => f x = v)).card) ^ 2 := by
  have key : ((s ×ˢ s).filter (fun x => f x.1 = f x.2)).card =
      ∑ v ∈ t, (((s ×ˢ s).filter (fun x => f x.1 = f x.2)).filter
        (fun x => f x.1 = v)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx
    exact hf _ hx.1.1
  rw [key]
  apply Finset.sum_congr rfl
  intro v _
  rw [sq, ← Finset.card_product]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hfx⟩
    exact ⟨⟨hx, hfx⟩, hy, hxy.symm.trans hfx⟩
  · rintro ⟨⟨hx, hfx⟩, hy, hfy⟩
    exact ⟨⟨⟨hx, hy⟩, hfx.trans hfy.symm⟩, hfx⟩

/-- `S₂(N) = ∑_{(p,q) coprime} ⌊N / max p q⌋²`. -/
theorem S2_eq_sum_prim (N : ℕ) : S2 N = ∑ v ∈ prim N, Fn N v := by
  have h1 : (rows2 N ×ˢ rows2 N).filter (fun x => x.1.1 * x.2.2 = x.1.2 * x.2.1) =
      (rows2 N ×ˢ rows2 N).filter (fun x => dir x.1 = dir x.2) := by
    apply Finset.filter_congr
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx
    simp only [rows2, entries, Finset.mem_product, Finset.mem_Icc] at hx
    exact mul_eq_mul_iff_dir_eq (a := a) (b := b) (c := c) (d := d) (by omega) (by omega)
  rw [S2, h1, card_pairs_eq_sum_sq (s := rows2 N) (t := prim N) (f := dir)
    (fun x hx => dir_mem_prim hx)]
  apply Finset.sum_congr rfl
  rintro ⟨p, q⟩ hpq
  rw [fiber_card hpq]
  rfl

/-! ### Counting directions -/

/-- There are `φ(p)` integers `q ∈ [1, p]` coprime to `p`. -/
lemma card_coprime_Icc (p : ℕ) :
    ((Finset.Icc 1 p).filter (Nat.Coprime p)).card = Nat.totient p := by
  have e : Finset.Ico 1 (1 + p) = Finset.Icc 1 p := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  rw [← e]
  exact Nat.filter_coprime_Ico_eq_totient p 1

/-- The directions below the diagonal contribute `∑ φ(m) ⌊N/m⌋²`. -/
lemma sum_primBelow (N : ℕ) :
    ∑ v ∈ primBelow N, Fn N v = ∑ m ∈ Finset.Icc 1 N, Nat.totient m * (N / m) ^ 2 := by
  rw [Finset.sum_finset_product (primBelow N) (Finset.Icc 1 N)
    (fun p => (Finset.Icc 1 p).filter (Nat.Coprime p))]
  · apply Finset.sum_congr rfl
    intro p _
    have hval : ∀ q ∈ (Finset.Icc 1 p).filter (Nat.Coprime p), Fn N (p, q) = (N / p) ^ 2 := by
      intro q hq
      have hqp : q ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
      simp only [Fn, max_eq_left hqp]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, card_coprime_Icc]
  · rintro ⟨p, q⟩
    simp only [primBelow, prim, rows2, entries, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hp1, hpN⟩, hq1, _⟩, hc⟩, hqp⟩
      exact ⟨⟨hp1, hpN⟩, ⟨hq1, hqp⟩, hc⟩
    · rintro ⟨⟨hp1, hpN⟩, ⟨hq1, hqp⟩, hc⟩
      exact ⟨⟨⟨⟨hp1, hpN⟩, hq1, le_trans hqp hpN⟩, hc⟩, hqp⟩

/-- The directions above the diagonal also contribute `∑ φ(m) ⌊N/m⌋²`. -/
lemma sum_primAbove (N : ℕ) :
    ∑ v ∈ primAbove N, Fn N v = ∑ m ∈ Finset.Icc 1 N, Nat.totient m * (N / m) ^ 2 := by
  rw [Finset.sum_finset_product_right (primAbove N) (Finset.Icc 1 N)
    (fun q => (Finset.Icc 1 q).filter (Nat.Coprime q))]
  · apply Finset.sum_congr rfl
    intro q _
    have hval : ∀ p ∈ (Finset.Icc 1 q).filter (Nat.Coprime q), Fn N (p, q) = (N / q) ^ 2 := by
      intro p hp
      have hpq : p ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      simp only [Fn, max_eq_right hpq]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, card_coprime_Icc]
  · rintro ⟨p, q⟩
    simp only [primAbove, prim, rows2, entries, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hp1, _⟩, hq1, hqN⟩, hc⟩, hpq⟩
      exact ⟨⟨hq1, hqN⟩, ⟨hp1, hpq⟩, hc.symm⟩
    · rintro ⟨⟨hq1, hqN⟩, ⟨hp1, hpq⟩, hc⟩
      exact ⟨⟨⟨⟨hp1, le_trans hpq hqN⟩, hq1, hqN⟩, hc.symm⟩, hpq⟩

/-- Every direction is below or above the diagonal. -/
lemma primBelow_union_primAbove (N : ℕ) : primBelow N ∪ primAbove N = prim N := by
  ext v
  simp only [primBelow, primAbove, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases le_total v.2 v.1 with hle | hle
    · exact Or.inl ⟨h, hle⟩
    · exact Or.inr ⟨h, hle⟩

/-- Only the direction `(1, 1)` is both below and above the diagonal. -/
lemma sum_primInter (N : ℕ) : ∑ v ∈ primBelow N ∩ primAbove N, Fn N v = N ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [Fn]
  · have hset : primBelow N ∩ primAbove N = {(1, 1)} := by
      ext ⟨p, q⟩
      simp only [primBelow, primAbove, prim, rows2, entries, Finset.mem_inter,
        Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨_, hc⟩, hqp⟩, _, hpq⟩
        have hpq' : p = q := le_antisymm hpq hqp
        rw [← hpq'] at hc
        have hp : p = 1 := (Nat.coprime_self p).mp hc
        exact ⟨hp, hpq'.symm.trans hp⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨⟨⟨⟨le_refl 1, hN⟩, le_refl 1, hN⟩, Nat.coprime_one_left 1⟩, le_refl 1⟩,
          ⟨⟨⟨le_refl 1, hN⟩, le_refl 1, hN⟩, Nat.coprime_one_left 1⟩, le_refl 1⟩
    rw [hset, Finset.sum_singleton]
    simp [Fn]

/-! ### Proposition 2.1 -/

/-- **Proposition 2.1**, in the form `S₂(N) + N² = 2 ∑_{m ≤ N} φ(m) ⌊N/m⌋²`. -/
theorem S2_add_sq (N : ℕ) :
    S2 N + N ^ 2 = 2 * ∑ m ∈ Finset.Icc 1 N, Nat.totient m * (N / m) ^ 2 := by
  have h : ∑ v ∈ primBelow N ∪ primAbove N, Fn N v + ∑ v ∈ primBelow N ∩ primAbove N, Fn N v =
      ∑ v ∈ primBelow N, Fn N v + ∑ v ∈ primAbove N, Fn N v := Finset.sum_union_inter
  rw [primBelow_union_primAbove, sum_primInter, sum_primBelow, sum_primAbove,
    ← S2_eq_sum_prim] at h
  rw [h]
  ring

/-- **Proposition 2.1**: `S₂(N) = 2 ∑_{m ≤ N} φ(m) ⌊N/m⌋² − N²`. -/
theorem S2_formula (N : ℕ) :
    S2 N = 2 * ∑ m ∈ Finset.Icc 1 N, Nat.totient m * (N / m) ^ 2 - N ^ 2 :=
  Nat.eq_sub_of_add_eq (S2_add_sq N)

end SingularMatrices
