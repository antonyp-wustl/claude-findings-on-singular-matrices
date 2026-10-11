import SingularMatrices.ThreeByThree

/-!
# The exact decomposition for 3×3 matrices (Section 3), part 2: grouping pairs by plane

* `S3_planes`: **Lemma 3.1**, plane form:
  `S₃(N) = N³ A(N) + ∑_P L_P I_P`.

A plane `P` is represented by its set of rows `P ∩ {1,…,N}³`, so `L_P = P.card`. The planes that
occur are those spanned by a pair of non-parallel rows (`planes3`). `I_P` (`IP`) is the number of
ordered pairs of non-parallel rows in `P`.
-/

namespace SingularMatrices

open Finset

/-- The ordered pairs of non-parallel rows. -/
def nonPar (N : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (rows3 N ×ˢ rows3 N).filter (fun x => ¬ cross3 x.1 x.2 = 0)

/-- The rows on the plane with normal `x.1 × x.2` (the plane spanned by `x`, if non-parallel). -/
def span3 (N : ℕ) (x : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  (rows3 N).filter (fun t => dot3 (cross3 x.1 x.2) t = 0)

/-- The planes spanned by pairs of non-parallel rows, each recorded by its set of rows. -/
def planes3 (N : ℕ) : Finset (Finset (ℕ × ℕ × ℕ)) := (nonPar N).image (span3 N)

/-- `I_P`: the number of ordered pairs of non-parallel rows in `P`. -/
def IP (P : Finset (ℕ × ℕ × ℕ)) : ℕ :=
  ((P ×ˢ P).filter (fun x => ¬ cross3 x.1 x.2 = 0)).card

/-- The cross product of two integer vectors. -/
def crossZ (u v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

lemma dot3_cross3_left (r s : ℕ × ℕ × ℕ) : dot3 (cross3 r s) r = 0 := by
  simp only [dot3, cross3]
  ring

lemma dot3_cross3_right (r s : ℕ × ℕ × ℕ) : dot3 (cross3 r s) s = 0 := by
  simp only [dot3, cross3]
  ring

/-- If `c ⟂ r` and `c ⟂ s`, then `c` is parallel to `r × s`. -/
lemma crossZ_cross3_eq_zero {c : ℤ × ℤ × ℤ} {r s : ℕ × ℕ × ℕ} (hr : dot3 c r = 0)
    (hs : dot3 c s = 0) : crossZ (cross3 r s) c = 0 := by
  obtain ⟨c1, c2, c3⟩ := c
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨s1, s2, s3⟩ := s
  simp only [dot3] at hr hs
  simp only [crossZ, cross3, Prod.mk_eq_zero]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (s1 : ℤ) * hr - (r1 : ℤ) * hs
  · linear_combination (s2 : ℤ) * hr - (r2 : ℤ) * hs
  · linear_combination (s3 : ℤ) * hr - (r3 : ℤ) * hs

/-- Parallel nonzero normals define the same plane. -/
lemma dot3_iff_of_crossZ_eq_zero {n m : ℤ × ℤ × ℤ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : crossZ n m = 0) (t : ℕ × ℕ × ℕ) : dot3 n t = 0 ↔ dot3 m t = 0 := by
  obtain ⟨n1, n2, n3⟩ := n
  obtain ⟨m1, m2, m3⟩ := m
  obtain ⟨t1, t2, t3⟩ := t
  simp only [crossZ, Prod.mk_eq_zero] at h
  obtain ⟨c1, c2, c3⟩ := h
  simp only [dot3]
  have e1 : (n1 * t1 + n2 * t2 + n3 * t3) * m1 = (m1 * t1 + m2 * t2 + m3 * t3) * n1 := by
    linear_combination (-(t2 : ℤ)) * c3 + (t3 : ℤ) * c2
  have e2 : (n1 * t1 + n2 * t2 + n3 * t3) * m2 = (m1 * t1 + m2 * t2 + m3 * t3) * n2 := by
    linear_combination (t1 : ℤ) * c3 - (t3 : ℤ) * c1
  have e3 : (n1 * t1 + n2 * t2 + n3 * t3) * m3 = (m1 * t1 + m2 * t2 + m3 * t3) * n3 := by
    linear_combination (-(t1 : ℤ)) * c2 + (t2 : ℤ) * c1
  constructor
  · intro hD
    by_contra hD'
    apply hn
    simp only [Prod.mk_eq_zero]
    refine ⟨?_, ?_, ?_⟩
    · have z : (m1 * t1 + m2 * t2 + m3 * t3) * n1 = 0 := by linear_combination -e1 + m1 * hD
      exact (mul_eq_zero.mp z).resolve_left hD'
    · have z : (m1 * t1 + m2 * t2 + m3 * t3) * n2 = 0 := by linear_combination -e2 + m2 * hD
      exact (mul_eq_zero.mp z).resolve_left hD'
    · have z : (m1 * t1 + m2 * t2 + m3 * t3) * n3 = 0 := by linear_combination -e3 + m3 * hD
      exact (mul_eq_zero.mp z).resolve_left hD'
  · intro hD'
    by_contra hD
    apply hm
    simp only [Prod.mk_eq_zero]
    refine ⟨?_, ?_, ?_⟩
    · have z : (n1 * t1 + n2 * t2 + n3 * t3) * m1 = 0 := by linear_combination e1 + n1 * hD'
      exact (mul_eq_zero.mp z).resolve_left hD
    · have z : (n1 * t1 + n2 * t2 + n3 * t3) * m2 = 0 := by linear_combination e2 + n2 * hD'
      exact (mul_eq_zero.mp z).resolve_left hD
    · have z : (n1 * t1 + n2 * t2 + n3 * t3) * m3 = 0 := by linear_combination e3 + n3 * hD'
      exact (mul_eq_zero.mp z).resolve_left hD

/-- Two non-parallel pairs, one lying on the plane of the other, span the same plane. -/
lemma span3_eq {N : ℕ} {x y : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hx : cross3 x.1 x.2 ≠ 0)
    (hy : cross3 y.1 y.2 ≠ 0) (h1 : dot3 (cross3 y.1 y.2) x.1 = 0)
    (h2 : dot3 (cross3 y.1 y.2) x.2 = 0) : span3 N x = span3 N y := by
  have hc : crossZ (cross3 x.1 x.2) (cross3 y.1 y.2) = 0 := crossZ_cross3_eq_zero h1 h2
  ext t
  simp only [span3, mem_filter]
  rw [dot3_iff_of_crossZ_eq_zero hx hy hc t]

lemma mem_span3_self {N : ℕ} {x : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hx : x ∈ rows3 N ×ˢ rows3 N) :
    x.1 ∈ span3 N x ∧ x.2 ∈ span3 N x := by
  have h := mem_product.mp hx
  exact ⟨mem_filter.mpr ⟨h.1, dot3_cross3_left _ _⟩, mem_filter.mpr ⟨h.2, dot3_cross3_right _ _⟩⟩

/-- The non-parallel pairs spanning `P` are exactly the non-parallel pairs of rows of `P`. -/
lemma card_fiber_span3 {N : ℕ} {P : Finset (ℕ × ℕ × ℕ)} (hP : P ∈ planes3 N) :
    ((nonPar N).filter (fun x => span3 N x = P)).card = IP P := by
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hP
  have hyc : ¬ cross3 y.1 y.2 = 0 := (mem_filter.mp hy).2
  rw [IP]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hxy⟩ := mem_filter.mp hx
    obtain ⟨hx2, hxc⟩ := mem_filter.mp hx1
    have h := mem_span3_self hx2
    rw [hxy] at h
    exact mem_filter.mpr ⟨mem_product.mpr h, hxc⟩
  · intro hx
    obtain ⟨hx1, hxc⟩ := mem_filter.mp hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx1
    obtain ⟨h1r, h1d⟩ := mem_filter.mp h1
    obtain ⟨h2r, h2d⟩ := mem_filter.mp h2
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨h1r, h2r⟩, hxc⟩, ?_⟩
    exact span3_eq hxc hyc h1d h2d

/-- **Lemma 3.1**, plane form: `S₃(N) = N³ A(N) + ∑_P L_P I_P`. -/
theorem S3_planes (N : ℕ) :
    S3 N = N ^ 3 * A3count N + ∑ P ∈ planes3 N, P.card * IP P := by
  rw [S3_split]
  congr 1
  have hmaps : ∀ x ∈ nonPar N, span3 N x ∈ planes3 N :=
    fun x hx => mem_image_of_mem (span3 N) hx
  change ∑ x ∈ nonPar N, Lw N (cross3 x.1 x.2) = _
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro P hP
  have h1 : ∀ x ∈ (nonPar N).filter (fun x => span3 N x = P),
      Lw N (cross3 x.1 x.2) = P.card := by
    intro x hx
    show (span3 N x).card = P.card
    rw [(mem_filter.mp hx).2]
  rw [sum_congr rfl h1, sum_const, smul_eq_mul, card_fiber_span3 hP]
  exact Nat.mul_comm _ _

end SingularMatrices
