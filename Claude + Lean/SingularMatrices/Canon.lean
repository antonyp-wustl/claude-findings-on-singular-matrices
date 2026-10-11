import SingularMatrices.Planes
import SingularMatrices.Moebius

/-!
# Indexing planes by canonical normals

A pair of non-parallel rows `(r, s)` spans the plane with normal `r × s`. Dividing out the gcd
(`primZ`) and fixing the sign so that the first nonzero entry is positive (`canonOf`) gives the
*canonical normal* `canon (r × s)`.

* `canon_eq_of_crossZ`: parallel nonzero vectors have the same canonical normal.
* `canon_cross_eq_iff`: a non-parallel pair has canonical normal `w` iff both rows are orthogonal
  to `w`.
* `S3_normals`: **Lemma 3.1** indexed by normals,
  `S₃(N) = N³ A(N) + ∑_w L(w) I(w)`, where `w` runs over the canonical normals with entries in
  `[-N², N²]` (`Wbox (N ^ 2)`), `L(w)` counts the rows orthogonal to `w`, and `I(w)` counts the
  ordered non-parallel pairs of such rows.
-/

namespace SingularMatrices

open Finset

/-- The gcd of the absolute values of the entries. -/
def gZ (n : ℤ × ℤ × ℤ) : ℕ := Nat.gcd n.1.natAbs (Nat.gcd n.2.1.natAbs n.2.2.natAbs)

/-- Divide out the gcd of the entries. -/
def primZ (n : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (n.1 / (gZ n : ℤ), n.2.1 / (gZ n : ℤ), n.2.2 / (gZ n : ℤ))

/-- Negate a vector. -/
def negZ (w : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-w.1, -w.2.1, -w.2.2)

/-- The first nonzero entry is positive. -/
def isCanon (w : ℤ × ℤ × ℤ) : Prop :=
  0 < w.1 ∨ (w.1 = 0 ∧ 0 < w.2.1) ∨ (w.1 = 0 ∧ w.2.1 = 0 ∧ 0 < w.2.2)

instance (w : ℤ × ℤ × ℤ) : Decidable (isCanon w) :=
  inferInstanceAs (Decidable (0 < w.1 ∨ (w.1 = 0 ∧ 0 < w.2.1) ∨ (w.1 = 0 ∧ w.2.1 = 0 ∧ 0 < w.2.2)))

/-- Choose the sign so that the first nonzero entry is positive. -/
def canonOf (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := if isCanon p then p else negZ p

/-- The canonical normal: primitive, first nonzero entry positive. -/
def canon (n : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := canonOf (primZ n)

/-! ### Basic facts -/

lemma gZ_pos {n : ℤ × ℤ × ℤ} (hn : n ≠ 0) : 0 < gZ n := by
  apply Nat.pos_of_ne_zero
  intro h
  apply hn
  obtain ⟨h1, h23⟩ := Nat.gcd_eq_zero_iff.mp h
  obtain ⟨h2, h3⟩ := Nat.gcd_eq_zero_iff.mp h23
  obtain ⟨a, b, c⟩ := n
  simp only [Prod.mk_eq_zero]
  exact ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2, Int.natAbs_eq_zero.mp h3⟩

/-- `n = gZ(n) • primZ(n)`, and `primZ n` is primitive. -/
lemma primZ_spec {n : ℤ × ℤ × ℤ} (hn : n ≠ 0) :
    n.1 = (gZ n : ℤ) * (primZ n).1 ∧ n.2.1 = (gZ n : ℤ) * (primZ n).2.1 ∧
      n.2.2 = (gZ n : ℤ) * (primZ n).2.2 ∧ gZ (primZ n) = 1 := by
  have hg := gZ_pos hn
  have d1 : (gZ n : ℤ) ∣ n.1 := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have d2 : (gZ n : ℤ) ∣ n.2.1 :=
    Int.ofNat_dvd_left.mpr ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
  have d3 : (gZ n : ℤ) ∣ n.2.2 :=
    Int.ofNat_dvd_left.mpr ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
  have e1 : (gZ n : ℤ) * (primZ n).1 = n.1 := Int.mul_ediv_cancel' d1
  have e2 : (gZ n : ℤ) * (primZ n).2.1 = n.2.1 := Int.mul_ediv_cancel' d2
  have e3 : (gZ n : ℤ) * (primZ n).2.2 = n.2.2 := Int.mul_ediv_cancel' d3
  have a1 : n.1.natAbs = gZ n * (primZ n).1.natAbs := by
    rw [← e1, Int.natAbs_mul, Int.natAbs_cast]
  have a2 : n.2.1.natAbs = gZ n * (primZ n).2.1.natAbs := by
    rw [← e2, Int.natAbs_mul, Int.natAbs_cast]
  have a3 : n.2.2.natAbs = gZ n * (primZ n).2.2.natAbs := by
    rw [← e3, Int.natAbs_mul, Int.natAbs_cast]
  refine ⟨e1.symm, e2.symm, e3.symm, ?_⟩
  have key : gZ n * 1 = gZ n * gZ (primZ n) := by
    rw [mul_one]
    show Nat.gcd n.1.natAbs (Nat.gcd n.2.1.natAbs n.2.2.natAbs) =
      gZ n * Nat.gcd (primZ n).1.natAbs (Nat.gcd (primZ n).2.1.natAbs (primZ n).2.2.natAbs)
    rw [a1, a2, a3, Nat.gcd_mul_left, Nat.gcd_mul_left]
  exact (Nat.eq_of_mul_eq_mul_left hg key).symm

lemma ne_zero_of_gZ_eq_one {p : ℤ × ℤ × ℤ} (h : gZ p = 1) : p ≠ 0 := by
  rintro rfl
  simp [gZ] at h

lemma dot3_negZ (w : ℤ × ℤ × ℤ) (t : ℕ × ℕ × ℕ) : dot3 (negZ w) t = -dot3 w t := by
  simp only [dot3, negZ]
  ring

lemma negZ_negZ (w : ℤ × ℤ × ℤ) : negZ (negZ w) = w := by
  obtain ⟨a, b, c⟩ := w
  simp only [negZ, neg_neg]

lemma gZ_negZ (w : ℤ × ℤ × ℤ) : gZ (negZ w) = gZ w := by
  simp only [gZ, negZ, Int.natAbs_neg]

lemma isCanon_negZ {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : isCanon (negZ p) ↔ ¬ isCanon p := by
  obtain ⟨a, b, c⟩ := p
  have h : ¬ (a = 0 ∧ b = 0 ∧ c = 0) := fun h => hp (by simp only [Prod.mk_eq_zero]; exact h)
  simp only [isCanon, negZ]
  omega

lemma canonOf_eq_of_or {p q : ℤ × ℤ × ℤ} (hp : p ≠ 0) (h : q = p ∨ q = negZ p) :
    canonOf q = canonOf p := by
  rcases h with rfl | rfl
  · rfl
  · unfold canonOf
    by_cases hc : isCanon p
    · have h1 : ¬ isCanon (negZ p) := fun h' => (isCanon_negZ hp).mp h' hc
      rw [if_neg h1, if_pos hc, negZ_negZ]
    · have h1 : isCanon (negZ p) := (isCanon_negZ hp).mpr hc
      rw [if_pos h1, if_neg hc]

lemma dot3_canonOf_iff (p : ℤ × ℤ × ℤ) (t : ℕ × ℕ × ℕ) :
    dot3 (canonOf p) t = 0 ↔ dot3 p t = 0 := by
  unfold canonOf
  split_ifs
  · exact Iff.rfl
  · rw [dot3_negZ, neg_eq_zero]

lemma isCanon_canonOf {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : isCanon (canonOf p) := by
  unfold canonOf
  split_ifs with h
  · exact h
  · exact (isCanon_negZ hp).mpr h

lemma gZ_canonOf (p : ℤ × ℤ × ℤ) : gZ (canonOf p) = gZ p := by
  unfold canonOf
  split_ifs
  · rfl
  · exact gZ_negZ p

lemma canonOf_self {w : ℤ × ℤ × ℤ} (h : isCanon w) : canonOf w = w := by
  unfold canonOf
  exact if_pos h

lemma primZ_of_gZ {w : ℤ × ℤ × ℤ} (h : gZ w = 1) : primZ w = w := by
  apply Prod.ext
  · show w.1 / ((gZ w : ℕ) : ℤ) = w.1
    rw [h, Nat.cast_one, Int.ediv_one]
  · apply Prod.ext
    · show w.2.1 / ((gZ w : ℕ) : ℤ) = w.2.1
      rw [h, Nat.cast_one, Int.ediv_one]
    · show w.2.2 / ((gZ w : ℕ) : ℤ) = w.2.2
      rw [h, Nat.cast_one, Int.ediv_one]

lemma dot3_primZ {n : ℤ × ℤ × ℤ} (hn : n ≠ 0) (t : ℕ × ℕ × ℕ) :
    dot3 n t = (gZ n : ℤ) * dot3 (primZ n) t := by
  obtain ⟨e1, e2, e3, -⟩ := primZ_spec hn
  simp only [dot3]
  linear_combination (t.1 : ℤ) * e1 + (t.2.1 : ℤ) * e2 + (t.2.2 : ℤ) * e3

/-- The canonical normal defines the same plane. -/
lemma dot3_canon_iff {n : ℤ × ℤ × ℤ} (hn : n ≠ 0) (t : ℕ × ℕ × ℕ) :
    dot3 (canon n) t = 0 ↔ dot3 n t = 0 := by
  have hG : (gZ n : ℤ) ≠ 0 := by exact_mod_cast (gZ_pos hn).ne'
  unfold canon
  rw [dot3_canonOf_iff, dot3_primZ hn t, mul_eq_zero, or_iff_right hG]

lemma Lw_canon {N : ℕ} {n : ℤ × ℤ × ℤ} (hn : n ≠ 0) : Lw N (canon n) = Lw N n := by
  unfold Lw
  congr 1
  apply filter_congr
  intro t _
  exact dot3_canon_iff hn t

/-! ### Parallel vectors have the same canonical normal -/

lemma cross_scale {G H n1 n2 n3 m1 m2 m3 p1 p2 p3 q1 q2 q3 : ℤ} (hGH : G * H ≠ 0)
    (en1 : n1 = G * p1) (en2 : n2 = G * p2) (en3 : n3 = G * p3)
    (em1 : m1 = H * q1) (em2 : m2 = H * q2) (em3 : m3 = H * q3)
    (c1 : n2 * m3 - n3 * m2 = 0) (c2 : n3 * m1 - n1 * m3 = 0) (c3 : n1 * m2 - n2 * m1 = 0) :
    p1 * q2 = p2 * q1 ∧ p1 * q3 = p3 * q1 ∧ p2 * q3 = p3 * q2 := by
  subst en1 en2 en3 em1 em2 em3
  have k1 : (G * H) * (p2 * q3 - p3 * q2) = 0 := by linear_combination c1
  have k2 : (G * H) * (p3 * q1 - p1 * q3) = 0 := by linear_combination c2
  have k3 : (G * H) * (p1 * q2 - p2 * q1) = 0 := by linear_combination c3
  have r1 := (mul_eq_zero.mp k1).resolve_left hGH
  have r2 := (mul_eq_zero.mp k2).resolve_left hGH
  have r3 := (mul_eq_zero.mp k3).resolve_left hGH
  exact ⟨by linarith, by linarith, by linarith⟩

lemma nat_dvd_of_gcd_one {d e x1 x2 x3 : ℕ} (h : Nat.gcd x1 (Nat.gcd x2 x3) = 1)
    (d1 : d ∣ e * x1) (d2 : d ∣ e * x2) (d3 : d ∣ e * x3) : d ∣ e := by
  have k : Nat.gcd (e * x1) (Nat.gcd (e * x2) (e * x3)) = e := by
    rw [Nat.gcd_mul_left, Nat.gcd_mul_left, h, mul_one]
  rw [← k]
  exact Nat.dvd_gcd d1 (Nat.dvd_gcd d2 d3)

/-- Parallel primitive vectors have the same absolute values. -/
lemma natAbs_eq_of_parallel {p1 p2 p3 q1 q2 q3 : ℤ}
    (hp : Nat.gcd p1.natAbs (Nat.gcd p2.natAbs p3.natAbs) = 1)
    (hq : Nat.gcd q1.natAbs (Nat.gcd q2.natAbs q3.natAbs) = 1)
    (h12 : p1 * q2 = p2 * q1) (h13 : p1 * q3 = p3 * q1) (h23 : p2 * q3 = p3 * q2) :
    p1.natAbs = q1.natAbs ∧ p2.natAbs = q2.natAbs ∧ p3.natAbs = q3.natAbs := by
  have n12 : p1.natAbs * q2.natAbs = p2.natAbs * q1.natAbs := by
    rw [← Int.natAbs_mul, ← Int.natAbs_mul, h12]
  have n13 : p1.natAbs * q3.natAbs = p3.natAbs * q1.natAbs := by
    rw [← Int.natAbs_mul, ← Int.natAbs_mul, h13]
  have n23 : p2.natAbs * q3.natAbs = p3.natAbs * q2.natAbs := by
    rw [← Int.natAbs_mul, ← Int.natAbs_mul, h23]
  set a1 := p1.natAbs
  set a2 := p2.natAbs
  set a3 := p3.natAbs
  set b1 := q1.natAbs
  set b2 := q2.natAbs
  set b3 := q3.natAbs
  refine ⟨Nat.dvd_antisymm ?_ ?_, Nat.dvd_antisymm ?_ ?_, Nat.dvd_antisymm ?_ ?_⟩
  · exact nat_dvd_of_gcd_one hp (dvd_mul_left a1 b1)
      (Dvd.intro b2 (n12.trans (mul_comm a2 b1))) (Dvd.intro b3 (n13.trans (mul_comm a3 b1)))
  · exact nat_dvd_of_gcd_one hq (dvd_mul_left b1 a1)
      (Dvd.intro a2 ((mul_comm b1 a2).trans n12.symm))
      (Dvd.intro a3 ((mul_comm b1 a3).trans n13.symm))
  · exact nat_dvd_of_gcd_one hp (Dvd.intro b1 (n12.symm.trans (mul_comm a1 b2)))
      (dvd_mul_left a2 b2) (Dvd.intro b3 (n23.trans (mul_comm a3 b2)))
  · exact nat_dvd_of_gcd_one hq (Dvd.intro a1 ((mul_comm b2 a1).trans n12))
      (dvd_mul_left b2 a2) (Dvd.intro a3 ((mul_comm b2 a3).trans n23.symm))
  · exact nat_dvd_of_gcd_one hp (Dvd.intro b1 (n13.symm.trans (mul_comm a1 b3)))
      (Dvd.intro b2 (n23.symm.trans (mul_comm a2 b3))) (dvd_mul_left a3 b3)
  · exact nat_dvd_of_gcd_one hq (Dvd.intro a1 ((mul_comm b3 a1).trans n13))
      (Dvd.intro a2 ((mul_comm b3 a2).trans n23)) (dvd_mul_left b3 a3)

/-- Parallel vectors with the same absolute values are equal or opposite. -/
lemma eq_or_neg_of_parallel {p1 p2 p3 q1 q2 q3 : ℤ} (hp : ¬ (p1 = 0 ∧ p2 = 0 ∧ p3 = 0))
    (a1 : p1.natAbs = q1.natAbs) (a2 : p2.natAbs = q2.natAbs) (a3 : p3.natAbs = q3.natAbs)
    (h12 : p1 * q2 = p2 * q1) (h13 : p1 * q3 = p3 * q1) (h23 : p2 * q3 = p3 * q2) :
    (q1 = p1 ∧ q2 = p2 ∧ q3 = p3) ∨ (q1 = -p1 ∧ q2 = -p2 ∧ q3 = -p3) := by
  by_cases hp1 : p1 = 0
  · have hq1 : q1 = 0 := by
      rw [hp1, Int.natAbs_zero] at a1
      exact Int.natAbs_eq_zero.mp a1.symm
    by_cases hp2 : p2 = 0
    · have hq2 : q2 = 0 := by
        rw [hp2, Int.natAbs_zero] at a2
        exact Int.natAbs_eq_zero.mp a2.symm
      rcases Int.natAbs_eq_natAbs_iff.mp a3.symm with h | h
      · exact Or.inl ⟨by rw [hq1, hp1], by rw [hq2, hp2], h⟩
      · exact Or.inr ⟨by rw [hq1, hp1, neg_zero], by rw [hq2, hp2, neg_zero], h⟩
    · rcases Int.natAbs_eq_natAbs_iff.mp a2.symm with h | h
      · have k : p2 * (q3 - p3) = 0 := by linear_combination h23 + p3 * h
        have := (mul_eq_zero.mp k).resolve_left hp2
        exact Or.inl ⟨by rw [hq1, hp1], h, by linarith⟩
      · have k : p2 * (q3 + p3) = 0 := by linear_combination h23 + p3 * h
        have := (mul_eq_zero.mp k).resolve_left hp2
        exact Or.inr ⟨by rw [hq1, hp1, neg_zero], h, by linarith⟩
  · rcases Int.natAbs_eq_natAbs_iff.mp a1.symm with h | h
    · have k2 : p1 * (q2 - p2) = 0 := by linear_combination h12 + p2 * h
      have k3 : p1 * (q3 - p3) = 0 := by linear_combination h13 + p3 * h
      have r2 := (mul_eq_zero.mp k2).resolve_left hp1
      have r3 := (mul_eq_zero.mp k3).resolve_left hp1
      exact Or.inl ⟨h, by linarith, by linarith⟩
    · have k2 : p1 * (q2 + p2) = 0 := by linear_combination h12 + p2 * h
      have k3 : p1 * (q3 + p3) = 0 := by linear_combination h13 + p3 * h
      have r2 := (mul_eq_zero.mp k2).resolve_left hp1
      have r3 := (mul_eq_zero.mp k3).resolve_left hp1
      exact Or.inr ⟨h, by linarith, by linarith⟩

/-- Parallel nonzero vectors have the same canonical normal. -/
theorem canon_eq_of_crossZ {n m : ℤ × ℤ × ℤ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : crossZ n m = 0) : canon n = canon m := by
  obtain ⟨en1, en2, en3, gp⟩ := primZ_spec hn
  obtain ⟨em1, em2, em3, gq⟩ := primZ_spec hm
  have hGH : (gZ n : ℤ) * (gZ m : ℤ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (gZ_pos hn).ne') (by exact_mod_cast (gZ_pos hm).ne')
  simp only [crossZ, Prod.mk_eq_zero] at h
  obtain ⟨c1, c2, c3⟩ := h
  obtain ⟨h12, h13, h23⟩ := cross_scale hGH en1 en2 en3 em1 em2 em3 c1 c2 c3
  obtain ⟨a1, a2, a3⟩ := natAbs_eq_of_parallel (p1 := (primZ n).1) (p2 := (primZ n).2.1)
    (p3 := (primZ n).2.2) (q1 := (primZ m).1) (q2 := (primZ m).2.1) (q3 := (primZ m).2.2)
    gp gq h12 h13 h23
  have hp0 : primZ n ≠ 0 := ne_zero_of_gZ_eq_one gp
  have hp' : ¬ ((primZ n).1 = 0 ∧ (primZ n).2.1 = 0 ∧ (primZ n).2.2 = 0) := by
    rintro ⟨k1, k2, k3⟩
    have g := gp
    unfold gZ at g
    rw [k1, k2, k3] at g
    simp at g
  have hor : primZ m = primZ n ∨ primZ m = negZ (primZ n) := by
    rcases eq_or_neg_of_parallel hp' a1 a2 a3 h12 h13 h23 with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · exact Or.inl (Prod.ext e1 (Prod.ext e2 e3))
    · exact Or.inr (Prod.ext e1 (Prod.ext e2 e3))
  exact (canonOf_eq_of_or hp0 hor).symm

/-! ### The box of canonical normals -/

/-- The canonical normals with entries in `[-B, B]`. -/
def Wbox (B : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B).filter
    (fun w => gZ w = 1 ∧ isCanon w)

lemma mem_Wbox {B : ℕ} {w : ℤ × ℤ × ℤ} : w ∈ Wbox B ↔
    ((-(B : ℤ) ≤ w.1 ∧ w.1 ≤ B) ∧ (-(B : ℤ) ≤ w.2.1 ∧ w.2.1 ≤ B) ∧
      (-(B : ℤ) ≤ w.2.2 ∧ w.2.2 ≤ B)) ∧ gZ w = 1 ∧ isCanon w := by
  simp only [Wbox, mem_filter, mem_product, mem_Icc]

lemma bound_of_mul {G p n B : ℤ} (hG : 1 ≤ G) (e : n = G * p) (hn : -B ≤ n ∧ n ≤ B) :
    -B ≤ p ∧ p ≤ B := by
  obtain ⟨hn1, hn2⟩ := hn
  rcases le_total 0 p with hp | hp
  · have k := mul_le_mul_of_nonneg_right hG hp
    constructor <;> linarith
  · have k := mul_le_mul_of_nonpos_right hG hp
    constructor <;> linarith

lemma cast_mul_le_sq {a b N : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    (a : ℤ) * b ≤ ((N ^ 2 : ℕ) : ℤ) := by
  have h : a * b ≤ N ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul ha hb
  exact_mod_cast h

lemma diff_bound {a b c d N : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    -((N ^ 2 : ℕ) : ℤ) ≤ (a : ℤ) * b - (c : ℤ) * d ∧
      (a : ℤ) * b - (c : ℤ) * d ≤ ((N ^ 2 : ℕ) : ℤ) := by
  have h1 := cast_mul_le_sq ha hb
  have h2 := cast_mul_le_sq hc hd
  have h3 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
  have h4 : (0 : ℤ) ≤ (c : ℤ) * d := by positivity
  constructor <;> linarith

lemma canonOf_box {B : ℤ} {p : ℤ × ℤ × ℤ} (h1 : -B ≤ p.1 ∧ p.1 ≤ B)
    (h2 : -B ≤ p.2.1 ∧ p.2.1 ≤ B) (h3 : -B ≤ p.2.2 ∧ p.2.2 ≤ B) :
    (-B ≤ (canonOf p).1 ∧ (canonOf p).1 ≤ B) ∧ (-B ≤ (canonOf p).2.1 ∧ (canonOf p).2.1 ≤ B) ∧
      (-B ≤ (canonOf p).2.2 ∧ (canonOf p).2.2 ≤ B) := by
  unfold canonOf
  split_ifs
  · exact ⟨h1, h2, h3⟩
  · show (-B ≤ -p.1 ∧ -p.1 ≤ B) ∧ (-B ≤ -p.2.1 ∧ -p.2.1 ≤ B) ∧ (-B ≤ -p.2.2 ∧ -p.2.2 ≤ B)
    obtain ⟨a1, a2⟩ := h1
    obtain ⟨b1, b2⟩ := h2
    obtain ⟨c1, c2⟩ := h3
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The canonical normal of a non-parallel pair lies in `Wbox (N ^ 2)`. -/
lemma canon_mem_Wbox {N : ℕ} {r s : ℕ × ℕ × ℕ} (hr : r ∈ rows3 N) (hs : s ∈ rows3 N)
    (hc : cross3 r s ≠ 0) : canon (cross3 r s) ∈ Wbox (N ^ 2) := by
  have hr' := mem_rows3.mp hr
  have hs' := mem_rows3.mp hs
  obtain ⟨e1, e2, e3, gp⟩ := primZ_spec hc
  have hG : (1 : ℤ) ≤ (gZ (cross3 r s) : ℤ) := by exact_mod_cast gZ_pos hc
  have b1 := bound_of_mul hG e1 (diff_bound hr'.2.1.2 hs'.2.2.2 hr'.2.2.2 hs'.2.1.2)
  have b2 := bound_of_mul hG e2 (diff_bound hr'.2.2.2 hs'.1.2 hr'.1.2 hs'.2.2.2)
  have b3 := bound_of_mul hG e3 (diff_bound hr'.1.2 hs'.2.1.2 hr'.2.1.2 hs'.1.2)
  have hp0 := ne_zero_of_gZ_eq_one gp
  refine mem_Wbox.mpr ⟨canonOf_box b1 b2 b3, ?_, isCanon_canonOf hp0⟩
  unfold canon
  rw [gZ_canonOf]
  exact gp

/-- A non-parallel pair has canonical normal `w` iff both rows are orthogonal to `w`. -/
lemma canon_cross_eq_iff {N B : ℕ} {w : ℤ × ℤ × ℤ} (hw : w ∈ Wbox B)
    {x : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hx : x ∈ nonPar N) :
    canon (cross3 x.1 x.2) = w ↔ dot3 w x.1 = 0 ∧ dot3 w x.2 = 0 := by
  have hxc : cross3 x.1 x.2 ≠ 0 := (mem_filter.mp hx).2
  obtain ⟨-, hg, hcan⟩ := mem_Wbox.mp hw
  have hw0 : w ≠ 0 := ne_zero_of_gZ_eq_one hg
  constructor
  · rintro rfl
    exact ⟨(dot3_canon_iff hxc _).mpr (dot3_cross3_left _ _),
      (dot3_canon_iff hxc _).mpr (dot3_cross3_right _ _)⟩
  · rintro ⟨h1, h2⟩
    have hc := crossZ_cross3_eq_zero h1 h2
    rw [canon_eq_of_crossZ hxc hw0 hc]
    unfold canon
    rw [primZ_of_gZ hg]
    exact canonOf_self hcan

/-! ### Lemma 3.1 indexed by normals -/

/-- `I(w)`: ordered non-parallel pairs of rows orthogonal to `w`. -/
def Iw (N : ℕ) (w : ℤ × ℤ × ℤ) : ℕ :=
  ((nonPar N).filter (fun x => dot3 w x.1 = 0 ∧ dot3 w x.2 = 0)).card

lemma Iw_eq_IP (N : ℕ) (w : ℤ × ℤ × ℤ) :
    Iw N w = IP ((rows3 N).filter (fun t => dot3 w t = 0)) := by
  unfold Iw IP
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hd1, hd2⟩ := mem_filter.mp hx
    obtain ⟨hx2, hxc⟩ := mem_filter.mp hx1
    obtain ⟨hr, hs⟩ := mem_product.mp hx2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hr, hd1⟩, mem_filter.mpr ⟨hs, hd2⟩⟩,
      hxc⟩
  · intro hx
    obtain ⟨hx1, hxc⟩ := mem_filter.mp hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx1
    obtain ⟨hr, hd1⟩ := mem_filter.mp h1
    obtain ⟨hs, hd2⟩ := mem_filter.mp h2
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hr, hs⟩, hxc⟩, hd1, hd2⟩

theorem sum_nonPar_eq (N : ℕ) :
    ∑ x ∈ nonPar N, Lw N (cross3 x.1 x.2) = ∑ w ∈ Wbox (N ^ 2), Lw N w * Iw N w := by
  have hmaps : ∀ x ∈ nonPar N, canon (cross3 x.1 x.2) ∈ Wbox (N ^ 2) := by
    intro x hx
    obtain ⟨hx1, hxc⟩ := mem_filter.mp hx
    obtain ⟨hr, hs⟩ := mem_product.mp hx1
    exact canon_mem_Wbox hr hs hxc
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro w hw
  have hL : ∀ x ∈ (nonPar N).filter (fun x => canon (cross3 x.1 x.2) = w),
      Lw N (cross3 x.1 x.2) = Lw N w := by
    intro x hx
    obtain ⟨hx1, hxw⟩ := mem_filter.mp hx
    rw [← hxw, Lw_canon (mem_filter.mp hx1).2]
  have hF : (nonPar N).filter (fun x => canon (cross3 x.1 x.2) = w) =
      (nonPar N).filter (fun x => dot3 w x.1 = 0 ∧ dot3 w x.2 = 0) :=
    filter_congr (fun x hx => canon_cross_eq_iff hw hx)
  rw [sum_congr rfl hL, sum_const, smul_eq_mul, hF]
  exact Nat.mul_comm _ _

/-- **Lemma 3.1**, indexed by canonical normals. -/
theorem S3_normals (N : ℕ) :
    S3 N = N ^ 3 * A3count N + ∑ w ∈ Wbox (N ^ 2), Lw N w * Iw N w := by
  rw [S3_split, ← sum_nonPar_eq]
  rfl

end SingularMatrices
