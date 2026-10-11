import SingularMatrices.FlatIntegral

/-!
# `αpw` is the area (the piecewise formula for `α(a, b)`, Section 4)

* `area_eq_αpw`: for `a, b > 0`,
  `area {(x, y) ∈ [0,1]² : a x + b y ≤ 1} = αpw a b`.

The area is computed by slicing: the slice at `x ∈ [0, 1]` is `[0, ψ(x)]` with
`ψ(x) = max 0 (min 1 ((1 - a x)/b))`, and `∫₀¹ ψ` is evaluated on each of the five regions.
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-- The region `{(x, y) ∈ [0,1]² : a x + b y ≤ 1}`. -/
def secSet (a b : ℝ) : Set (ℝ × ℝ) :=
  (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p | a * p.1 + b * p.2 ≤ 1}

/-- The height of the slice of `secSet a b` at `x`. -/
noncomputable def psi (a b x : ℝ) : ℝ := max 0 (min 1 ((1 - a * x) / b))

lemma continuous_psi (a b : ℝ) : Continuous (psi a b) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub (continuous_const.mul continuous_id)).div_const b))

lemma psi_eq_one {a b x : ℝ} (hb : 0 < b) (h : a * x ≤ 1 - b) : psi a b x = 1 := by
  unfold psi
  rw [min_eq_left ((le_div_iff₀ hb).mpr (by linarith)), max_eq_right zero_le_one]

lemma psi_eq_lin {a b x : ℝ} (hb : 0 < b) (h1 : 1 - b ≤ a * x) (h2 : a * x ≤ 1) :
    psi a b x = (1 - a * x) / b := by
  have hq1 : (1 - a * x) / b ≤ 1 := (div_le_one hb).mpr (by linarith)
  have hq0 : 0 ≤ (1 - a * x) / b := div_nonneg (by linarith) hb.le
  unfold psi
  rw [min_eq_right hq1, max_eq_right hq0]

lemma psi_eq_zero {a b x : ℝ} (hb : 0 < b) (h : 1 ≤ a * x) : psi a b x = 0 := by
  have hq : (1 - a * x) / b ≤ 0 := (div_le_iff₀ hb).mpr (by linarith)
  unfold psi
  rw [min_eq_right (by linarith), max_eq_left hq]

lemma int_psi_one {a b u v : ℝ} (huv : u ≤ v) (hf : ∀ x ∈ Icc u v, psi a b x = 1) :
    ∫ x in u..v, psi a b x = v - u := by
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
    (fun x hx => by rw [uIcc_of_le huv] at hx; exact hf x hx)]
  simp

lemma int_psi_zero {a b u v : ℝ} (huv : u ≤ v) (hf : ∀ x ∈ Icc u v, psi a b x = 0) :
    ∫ x in u..v, psi a b x = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
    (fun x hx => by rw [uIcc_of_le huv] at hx; exact hf x hx)]
  simp

lemma int_lin (a b u v : ℝ) :
    ∫ x in u..v, (1 - a * x) / b = ((v - u) - a * (v ^ 2 - u ^ 2) / 2) / b := by
  have hd : ∀ x ∈ uIcc u v, HasDerivAt (fun y : ℝ => (y - a / 2 * y ^ 2) / b)
      ((1 - a * x) / b) x := by
    intro x _
    exact (((hasDerivAt_id x).sub ((hasDerivAt_pow_succ' 1 x).const_mul (a / 2))).div_const
      b).congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => (1 - a * x) / b).intervalIntegrable u v)]
  ring

lemma int_psi_lin {a b u v : ℝ} (huv : u ≤ v)
    (hf : ∀ x ∈ Icc u v, psi a b x = (1 - a * x) / b) :
    ∫ x in u..v, psi a b x = ((v - u) - a * (v ^ 2 - u ^ 2) / 2) / b := by
  rw [intervalIntegral.integral_congr (g := fun x => (1 - a * x) / b)
    (fun x hx => by rw [uIcc_of_le huv] at hx; exact hf x hx), int_lin]

set_option maxHeartbeats 1000000 in
/-- `∫₀¹ ψ = αpw a b`, region by region. -/
lemma integral_psi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, psi a b x = αpw a b := by
  have hI : ∀ u v : ℝ, IntervalIntegrable (psi a b) volume u v :=
    fun u v => (continuous_psi a b).intervalIntegrable u v
  unfold αpw
  split_ifs with h1 h2 h3 h4
  · -- region I: `a + b ≤ 1`
    rw [int_psi_one zero_le_one (fun x hx => psi_eq_one hb (by nlinarith [hx.1, hx.2]))]
    norm_num
  · -- region II: `a, b ≤ 1 < a + b`
    have hx1 : 0 ≤ (1 - b) / a := div_nonneg (by linarith [h2.2]) ha.le
    have hx1' : (1 - b) / a ≤ 1 := (div_le_one ha).mpr (by linarith [not_le.mp h1])
    have ex1 : a * ((1 - b) / a) = 1 - b := by field_simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 ((1 - b) / a))
      (hI ((1 - b) / a) 1)]
    rw [int_psi_one hx1 (fun x hx => psi_eq_one hb (by
        have := mul_le_mul_of_nonneg_left hx.2 ha.le; linarith)),
      int_psi_lin hx1' (fun x hx => psi_eq_lin hb (by
        have := mul_le_mul_of_nonneg_left hx.1 ha.le; linarith)
        (by have := mul_le_mul_of_nonneg_left hx.2 ha.le; linarith [h2.1]))]
    field_simp
    ring
  · -- region III: `b ≤ 1 < a`
    have ha1 : 1 < a := by
      by_contra hc
      exact h2 ⟨not_lt.mp hc, h3⟩
    have hx1 : 0 ≤ (1 - b) / a := div_nonneg (by linarith) ha.le
    have hx10 : (1 - b) / a ≤ 1 / a := (div_le_div_iff_of_pos_right ha).mpr (by linarith)
    have hx0 : 1 / a ≤ 1 := (div_le_one ha).mpr ha1.le
    have ex1 : a * ((1 - b) / a) = 1 - b := by field_simp
    have ex0 : a * (1 / a) = 1 := by field_simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 ((1 - b) / a))
      (hI ((1 - b) / a) 1),
      ← intervalIntegral.integral_add_adjacent_intervals (hI ((1 - b) / a) (1 / a)) (hI (1 / a) 1)]
    rw [int_psi_one hx1 (fun x hx => psi_eq_one hb (by
        have := mul_le_mul_of_nonneg_left hx.2 ha.le; linarith)),
      int_psi_lin hx10 (fun x hx => psi_eq_lin hb (by
        have := mul_le_mul_of_nonneg_left hx.1 ha.le; linarith)
        (by have := mul_le_mul_of_nonneg_left hx.2 ha.le; linarith)),
      int_psi_zero hx0 (fun x hx => psi_eq_zero hb (by
        have := mul_le_mul_of_nonneg_left hx.1 ha.le; linarith))]
    field_simp
    ring
  · -- region III': `a ≤ 1 < b`
    have hb1 : 1 < b := not_le.mp h3
    rw [int_psi_lin zero_le_one (fun x hx => psi_eq_lin hb (by nlinarith [hx.1, hx.2])
      (by nlinarith [hx.1, hx.2]))]
    ring
  · -- region IV: `a, b > 1`
    have ha1 : 1 < a := not_le.mp h4
    have hb1 : 1 < b := not_le.mp h3
    have hx0 : 0 ≤ 1 / a := div_nonneg zero_le_one ha.le
    have hx0' : 1 / a ≤ 1 := (div_le_one ha).mpr ha1.le
    have ex0 : a * (1 / a) = 1 := by field_simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 (1 / a)) (hI (1 / a) 1)]
    rw [int_psi_lin hx0 (fun x hx => psi_eq_lin hb (by nlinarith [hx.1])
        (by have := mul_le_mul_of_nonneg_left hx.2 ha.le; linarith)),
      int_psi_zero hx0' (fun x hx => psi_eq_zero hb (by
        have := mul_le_mul_of_nonneg_left hx.1 ha.le; linarith))]
    field_simp
    ring

lemma measurableSet_secSet (a b : ℝ) : MeasurableSet (secSet a b) :=
  (measurableSet_Icc.prod measurableSet_Icc).inter (measurableSet_le (by fun_prop) measurable_const)

/-- The area of `{(x, y) ∈ [0,1]² : a x + b y ≤ 1}` is `αpw a b`. -/
theorem area_eq_αpw {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (volume (secSet a b)).toReal = αpw a b := by
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' secSet a b) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (psi a b x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hset : Prod.mk x ⁻¹' secSet a b = Icc 0 (min 1 ((1 - a * x) / b)) := by
        ext y
        simp only [secSet, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, mem_ofPred_eq,
          Set.mem_Icc, le_min_iff]
        constructor
        · rintro ⟨⟨_, hy0, hy1⟩, hxy⟩
          exact ⟨hy0, hy1, (le_div_iff₀ hb).mpr (by linarith)⟩
        · rintro ⟨hy0, hy1, hyq⟩
          have h := (le_div_iff₀ hb).mp hyq
          exact ⟨⟨hx, hy0, hy1⟩, by linarith⟩
      rw [hset, Real.volume_Icc, sub_zero]
      unfold psi
      rcases le_total (min 1 ((1 - a * x) / b)) 0 with h | h
      · rw [ENNReal.ofReal_of_nonpos h, max_eq_left h, ENNReal.ofReal_zero]
      · rw [max_eq_right h]
    · rw [Set.indicator_of_notMem hx]
      have hset : Prod.mk x ⁻¹' secSet a b = ∅ := by
        ext y
        simp only [secSet, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
          Set.mem_empty_iff_false, iff_false]
        intro h
        exact hx h.1.1
      rw [hset, measure_empty]
  have hnn : ∀ x, 0 ≤ psi a b x := fun x => le_max_left _ _
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_secSet a b),
    lintegral_congr hslice, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal ((continuous_psi a b).integrableOn_Icc)
      (Filter.Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc (fun x _ => hnn x)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_psi ha hb]

end SingularMatrices
