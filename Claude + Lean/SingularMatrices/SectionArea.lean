import SingularMatrices.AreaFormula

/-!
# Plane sections of the unit cube (Section 4)

For a vector `u ∈ ℝ³`, `sec u = u^⊥ ∩ [0,1]³` is the section of the unit cube by the plane through
`0` with normal `u`, and

  `areaSec u = μHE[2] (sec u)`

is its area, measured by Mathlib's 2-dimensional Euclidean Hausdorff measure (normalized to agree
with Lebesgue measure on planes). This is the paper's `α(u)`.

* `areaSec_wvec`: for `a, b > 0` and `w = (a, b, -1)`,
  `areaSec w = √(1 + a² + b²) · αpw a b`.

The section is the image of `{(x, y) ∈ [0,1]² : a x + b y ≤ 1}` under the linear map
`(x, y) ↦ (x, y, a x + b y)`, and Mathlib's area formula for linear maps
(`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`) scales area by the square root
of the Gram determinant, here `1 + a² + b²`.
-/

namespace SingularMatrices

open MeasureTheory Set Real

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The unit cube `[0,1]³`. -/
def cube : Set E3 := {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}

/-- The section of the cube by the plane through `0` with normal `u`. -/
def sec (u : E3) : Set E3 := {x | inner ℝ u x = 0} ∩ cube

/-- `α(u)`: the area of the section, by the 2-dimensional Euclidean Hausdorff measure. -/
noncomputable def areaSec (u : E3) : ℝ := (Measure.euclideanHausdorffMeasure 2 (sec u)).toReal

lemma mem_cube {x : E3} : x ∈ cube ↔ (0 ≤ x.ofLp 0 ∧ x.ofLp 0 ≤ 1) ∧
    (0 ≤ x.ofLp 1 ∧ x.ofLp 1 ≤ 1) ∧ (0 ≤ x.ofLp 2 ∧ x.ofLp 2 ≤ 1) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

lemma inner_E3 (x y : E3) :
    inner ℝ x y = x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1 + x.ofLp 2 * y.ofLp 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Rescaling the normal does not change the plane. -/
lemma sec_smul {u : E3} {c : ℝ} (hc : c ≠ 0) : sec (c • u) = sec u := by
  ext x
  simp only [sec, mem_inter_iff, mem_ofPred_eq, real_inner_smul_left, mul_eq_zero, hc, false_or]

lemma areaSec_smul {u : E3} {c : ℝ} (hc : c ≠ 0) : areaSec (c • u) = areaSec u := by
  unfold areaSec
  rw [sec_smul hc]

/-! ### The normal `(a, b, -1)` and the graph map -/

/-- The normal vector `(a, b, -1)`. -/
def wvec (a b : ℝ) : E3 := WithLp.toLp 2 ![a, b, -1]

lemma wvec0 (a b : ℝ) : (wvec a b).ofLp 0 = a := rfl
lemma wvec1 (a b : ℝ) : (wvec a b).ofLp 1 = b := rfl
lemma wvec2 (a b : ℝ) : (wvec a b).ofLp 2 = -1 := rfl

lemma inner_wvec (a b : ℝ) (x : E3) :
    inner ℝ (wvec a b) x = a * x.ofLp 0 + b * x.ofLp 1 - x.ofLp 2 := by
  rw [inner_E3, wvec0, wvec1, wvec2]
  ring

/-- The matrix of `(x, y) ↦ (x, y, a x + b y)`. -/
def gmat (a b : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; a, b]

/-- The graph map `(x, y) ↦ (x, y, a x + b y)`. -/
noncomputable def gLin (a b : ℝ) : E2 →ₗ[ℝ] E3 := Matrix.toLpLin 2 2 (gmat a b)

lemma gLin_ofLp (a b : ℝ) (p : E2) :
    (gLin a b p).ofLp = ![p.ofLp 0, p.ofLp 1, a * p.ofLp 0 + b * p.ofLp 1] := by
  rw [gLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [gmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma gLin_ofLp0 (a b : ℝ) (p : E2) : (gLin a b p).ofLp 0 = p.ofLp 0 :=
  (congrFun (gLin_ofLp a b p) 0).trans rfl

lemma gLin_ofLp1 (a b : ℝ) (p : E2) : (gLin a b p).ofLp 1 = p.ofLp 1 :=
  (congrFun (gLin_ofLp a b p) 1).trans rfl

lemma gLin_ofLp2 (a b : ℝ) (p : E2) :
    (gLin a b p).ofLp 2 = a * p.ofLp 0 + b * p.ofLp 1 :=
  (congrFun (gLin_ofLp a b p) 2).trans rfl

/-- The graph map scales area by `√(1 + a² + b²)`. -/
lemma normDet_gLin (a b : ℝ) : (gLin a b).normDet = √(1 + a ^ 2 + b ^ 2) := by
  have h := LinearMap.normDet_sq_eq_det_gram (gLin a b) (EuclideanSpace.basisFun (Fin 2) ℝ)
  rw [Matrix.det_fin_two] at h
  -- expand the inner products in coordinates first, so `simp` cannot turn them into norms
  simp only [Matrix.gram_apply, inner_E3, gLin_ofLp0, gLin_ofLp1, gLin_ofLp2] at h
  simp at h
  have hsq : (gLin a b).normDet ^ 2 = 1 + a ^ 2 + b ^ 2 := by linear_combination h
  rw [← hsq, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-! ### The section is the image of the flat region -/

/-- The flat region `{(x, y) ∈ [0,1]² : a x + b y ≤ 1}` in `ℝ²`. -/
def T2 (a b : ℝ) : Set E2 :=
  WithLp.ofLp ⁻¹' (MeasurableEquiv.finTwoArrow ⁻¹' secSet a b)

lemma mem_T2 {a b : ℝ} {p : E2} :
    p ∈ T2 a b ↔ (0 ≤ p.ofLp 0 ∧ p.ofLp 0 ≤ 1) ∧ (0 ≤ p.ofLp 1 ∧ p.ofLp 1 ≤ 1) ∧
      a * p.ofLp 0 + b * p.ofLp 1 ≤ 1 := by
  simp only [T2, secSet, Set.mem_preimage, MeasurableEquiv.finTwoArrow_apply, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_Icc, mem_ofPred_eq, and_assoc]

lemma volume_T2 (a b : ℝ) : volume (T2 a b) = volume (secSet a b) := by
  have h1 := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (((measurableSet_secSet a b).preimage
      (MeasurableEquiv.finTwoArrow (α := ℝ)).measurable).nullMeasurableSet)
  have h2 := (volume_preserving_finTwoArrow ℝ).measure_preimage
    (measurableSet_secSet a b).nullMeasurableSet
  exact h1.trans h2

lemma sec_wvec {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : sec (wvec a b) = gLin a b '' T2 a b := by
  ext x
  constructor
  · rintro ⟨hx, hcube⟩
    have hin : a * x.ofLp 0 + b * x.ofLp 1 - x.ofLp 2 = 0 := by
      rw [← inner_wvec]
      exact hx
    obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨_, h21⟩⟩ := mem_cube.mp hcube
    refine ⟨WithLp.toLp 2 ![x.ofLp 0, x.ofLp 1], ?_, ?_⟩
    · rw [mem_T2]
      exact ⟨⟨h00, h01⟩, ⟨h10, h11⟩,
        (show a * x.ofLp 0 + b * x.ofLp 1 ≤ 1 by linarith)⟩
    · apply PiLp.ext
      intro i
      rw [gLin_ofLp]
      fin_cases i <;> simp <;> linarith
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, h2⟩ := mem_T2.mp hp
    refine ⟨?_, ?_⟩
    · show inner ℝ (wvec a b) (gLin a b p) = 0
      rw [inner_wvec, gLin_ofLp0, gLin_ofLp1, gLin_ofLp2]
      ring
    · rw [mem_cube, gLin_ofLp0, gLin_ofLp1, gLin_ofLp2]
      have : 0 ≤ a * p.ofLp 0 + b * p.ofLp 1 :=
        add_nonneg (mul_nonneg ha.le h00) (mul_nonneg hb.le h10)
      exact ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨this, h2⟩⟩

/-- **The area of a plane section**: for `w = (a, b, -1)` with `a, b > 0`,
`α(w) = √(1 + a² + b²) · αpw a b`. -/
theorem areaSec_wvec {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    areaSec (wvec a b) = √(1 + a ^ 2 + b ^ 2) * αpw a b := by
  have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (gLin a b) (T2 a b)
  rw [finrank_euclideanSpace_fin] at h
  unfold areaSec
  rw [sec_wvec ha hb, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _),
    normDet_gLin, volume_T2, area_eq_αpw ha hb]

end SingularMatrices
