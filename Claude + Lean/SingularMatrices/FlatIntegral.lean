import SingularMatrices.RegionII

/-!
# The flat integral `∫∫ α(a,b)³ da db = 15/2 - 5π²/8` (Lemmas 4.2–4.4)

`αpw a b` is the piecewise formula for `α(a, b) = area {(x, y) ∈ [0,1]² : a x + b y ≤ 1}` on
`a, b > 0` (regions I, II, III, III', IV of the paper). We prove

* `flat_integral`: `∫_{b>0} ∫_{a>0} αpw(a, b)³ da db = 15/2 - 5π²/8`.

Regions I, III, III', IV contribute `1/2 + 15/64 + 15/64 + 1/32 = 1`, and region II contributes
`13/2 - 5π²/8` (`regionII`). The passage from the region-II integral in the coordinates
`(b, s = a + b - 1)` to the coordinates `(s, b)` of `regionII` is a change of order of
integration over a triangle (`triangle_swap`).

That `αpw` is the area and the chart identity `J = 6 ∫∫ α³` are in `AreaFormula`, `SectionArea`, `Octants`, `OctantIntegral` and `SphereIntegral`.
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-- The piecewise formula for `α(a, b)` on `a, b > 0`. -/
noncomputable def αpw (a b : ℝ) : ℝ :=
  if a + b ≤ 1 then 1
  else if a ≤ 1 ∧ b ≤ 1 then 1 - (a + b - 1) ^ 2 / (2 * a * b)
  else if b ≤ 1 then (1 - b / 2) / a
  else if a ≤ 1 then (1 - a / 2) / b
  else 1 / (2 * a * b)

/-! ### Elementary integrals -/

lemma integral_one_sub : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
    intro x _
    exact ((hasDerivAt_id x).sub ((hasDerivAt_pow_succ' 1 x).div_const 2)).congr_deriv
      (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => 1 - x).intervalIntegrable 0 1)]
  norm_num

lemma integral_one_sub_half_cube : ∫ x in (0 : ℝ)..1, (1 - x / 2) ^ 3 = 15 / 32 := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun y : ℝ => y - 3 * y ^ 2 / 4 + y ^ 3 / 4 - y ^ 4 / 32) ((1 - x / 2) ^ 3) x := by
    intro x _
    exact ((((hasDerivAt_id x).sub (((hasDerivAt_pow_succ' 1 x).const_mul 3).div_const 4)).add
      ((hasDerivAt_pow_succ' 2 x).div_const 4)).sub
      ((hasDerivAt_pow_succ' 3 x).div_const 32)).congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => (1 - x / 2) ^ 3).intervalIntegrable 0 1)]
  norm_num

lemma inv_cube_eq_rpow {a : ℝ} (ha : 0 < a) : (a ^ 3)⁻¹ = a ^ (-3 : ℝ) := by
  rw [Real.rpow_neg ha.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma integrableOn_Ioi_inv_cube : IntegrableOn (fun a : ℝ => (a ^ 3)⁻¹) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).congr_fun
    (fun a ha => (inv_cube_eq_rpow (lt_trans one_pos ha)).symm) measurableSet_Ioi

lemma integral_Ioi_inv_cube : ∫ a in Ioi (1 : ℝ), (a ^ 3)⁻¹ = 1 / 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun a ha => inv_cube_eq_rpow (lt_trans one_pos ha)),
    integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos]
  norm_num

/-! ### Bounds and measurability -/

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x ∈ Ioc a b, |f x| ≤ M) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact hM x hx

lemma measurable_αpw (b : ℝ) : Measurable (fun a => αpw a b) := by
  unfold αpw
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
    (Measurable.ite ?_ (by fun_prop)
      (Measurable.ite (MeasurableSet.const _) (by fun_prop)
        (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
          (by fun_prop))))
  show MeasurableSet ({a : ℝ | a ≤ 1} ∩ {_a : ℝ | b ≤ 1})
  exact (measurableSet_le measurable_id measurable_const).inter (MeasurableSet.const _)

lemma αpw_mem {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ≤ αpw a b ∧ αpw a b ≤ 1 := by
  unfold αpw
  by_cases h1 : a + b ≤ 1
  · rw [if_pos h1]
    exact ⟨zero_le_one, le_rfl⟩
  · rw [if_neg h1, if_pos ⟨ha1, hb1⟩]
    have ht : 0 < a + b - 1 := by linarith [not_le.mp h1]
    have hta : a + b - 1 ≤ a := by linarith
    have htb : a + b - 1 ≤ b := by linarith
    have hD : 0 ≤ 2 * a * b := (mul_pos (mul_pos two_pos ha) hb).le
    have hss : (a + b - 1) ^ 2 ≤ 2 * a * b := by
      have h := mul_le_mul hta htb ht.le ha.le
      nlinarith
    have hq0 := div_nonneg (sq_nonneg (a + b - 1)) hD
    have hq1 := div_le_one_of_le₀ hss hD
    constructor <;> linarith

lemma f2_bound (s b : ℝ) (hs : 0 ≤ s) (hsb : s ≤ b) (hb : b ≤ 1) : |f2 s b| ≤ 1 := by
  have hb0 : 0 ≤ b := le_trans hs hsb
  have hd : s ≤ 1 + s - b := by linarith
  have hd0 : 0 ≤ 1 + s - b := le_trans hs hd
  have hD : 0 ≤ 2 * b * (1 + s - b) := mul_nonneg (mul_nonneg (by norm_num) hb0) hd0
  have hss : s ^ 2 ≤ 2 * b * (1 + s - b) := by
    have h1 : s * s ≤ b * (1 + s - b) := mul_le_mul hsb hd hs hb0
    have h2 : 0 ≤ b * (1 + s - b) := mul_nonneg hb0 hd0
    nlinarith
  have hq0 : 0 ≤ s ^ 2 / (2 * b * (1 + s - b)) := div_nonneg (sq_nonneg s) hD
  have hq1 : s ^ 2 / (2 * b * (1 + s - b)) ≤ 1 := div_le_one_of_le₀ hss hD
  have h0 : 0 ≤ 1 - s ^ 2 / (2 * b * (1 + s - b)) := by linarith
  have h1 : 1 - s ^ 2 / (2 * b * (1 + s - b)) ≤ 1 := by linarith
  unfold f2
  rw [abs_of_nonneg (pow_nonneg h0 3)]
  exact pow_le_one₀ h0 h1

lemma measurable_f2 : Measurable (Function.uncurry f2) := by
  show Measurable (fun p : ℝ × ℝ => (1 - p.1 ^ 2 / (2 * p.2 * (1 + p.1 - p.2))) ^ 3)
  fun_prop

/-! ### Changing the order of integration over a triangle -/

/-- `g s b` on the triangle `s ≤ b`, and `0` elsewhere. -/
noncomputable def triG (g : ℝ → ℝ → ℝ) (b s : ℝ) : ℝ := if s ≤ b then g s b else 0

/-- `∫₀¹ ∫₀ᵇ g s b ds db = ∫₀¹ ∫ₛ¹ g s b db ds` for `g` measurable and bounded on the triangle. -/
lemma triangle_swap (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (C : ℝ)
    (hbd : ∀ s b, 0 ≤ s → s ≤ b → b ≤ 1 → |g s b| ≤ C) :
    IntervalIntegrable (fun b => ∫ s in (0 : ℝ)..b, g s b) volume 0 1 ∧
    ∫ b in (0 : ℝ)..1, (∫ s in (0 : ℝ)..b, g s b) =
      ∫ s in (0 : ℝ)..1, (∫ b in s..1, g s b) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hbd 0 0 le_rfl le_rfl zero_le_one)
  have hGm : Measurable (Function.uncurry (triG g)) := by
    have e : Function.uncurry (triG g) =
        fun p : ℝ × ℝ => if p.2 ≤ p.1 then g p.2 p.1 else 0 := by
      funext p
      rfl
    rw [e]
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hg.comp (measurable_snd.prodMk measurable_fst)) measurable_const
  have hGi : Integrable (Function.uncurry (triG g))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Integrable.mono' (integrable_const C) hGm.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    rw [Set.mem_prod] at hp
    obtain ⟨⟨_, hb1⟩, ⟨hs0, _⟩⟩ := hp
    show ‖triG g p.1 p.2‖ ≤ C
    unfold triG
    split_ifs with h
    · rw [Real.norm_eq_abs]
      exact hbd _ _ hs0.le h hb1
    · simpa using hC
  have hL : ∀ b ∈ Ioc (0 : ℝ) 1, ∫ s in (0 : ℝ)..b, g s b = ∫ s in Ioc (0 : ℝ) 1, triG g b s := by
    intro b hb
    rw [intervalIntegral.integral_of_le hb.1.le]
    have h1 : EqOn (fun s => triG g b s) ((Iic b).indicator (fun s => g s b)) (Ioc 0 1) := by
      intro s _
      simp only [triG, Set.indicator_apply, Set.mem_Iic]
    rw [setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_indicator measurableSet_Iic]
    have hset : Ioc (0 : ℝ) 1 ∩ Iic b = Ioc 0 b := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, le_trans h2 hb.2⟩, h2⟩
    rw [hset]
  have hR : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ b in s..1, g s b = ∫ b in Ioc (0 : ℝ) 1, triG g b s := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.2]
    have h1 : EqOn (fun b => triG g b s) ((Ici s).indicator (fun b => g s b)) (Ioc 0 1) := by
      intro b _
      simp only [triG, Set.indicator_apply, Set.mem_Ici]
    rw [setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_indicator measurableSet_Ici]
    have hset : Ioc (0 : ℝ) 1 ∩ Ici s = Icc s 1 := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨lt_of_lt_of_le hs.1 h1, h2⟩, h1⟩
    rw [hset, integral_Icc_eq_integral_Ioc]
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact IntegrableOn.congr_fun hGi.integral_prod_left (fun b hb => (hL b hb).symm)
      measurableSet_Ioc
  · rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hL,
      intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hR]
    exact integral_integral_swap hGi

/-! ### The inner integrals -/

lemma inner_small {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 =
      (1 - b) + (∫ s in (0 : ℝ)..b, f2 s b) + (1 - b / 2) ^ 3 / 2 := by
  have hm : Measurable (fun a => αpw a b ^ 3) := (measurable_αpw b).pow_const 3
  have hbd : ∀ a ∈ Ioc (0 : ℝ) 1, |αpw a b ^ 3| ≤ 1 := fun a ha => by
    obtain ⟨h0, h1⟩ := αpw_mem ha.1 ha.2 hb hb1
    rw [abs_of_nonneg (pow_nonneg h0 3)]
    exact pow_le_one₀ h0 h1
  -- the part `a > 1` (region III)
  have hEq3 : EqOn (fun a => αpw a b ^ 3) (fun a => (1 - b / 2) ^ 3 * (a ^ 3)⁻¹) (Ioi 1) := by
    intro a ha
    have ha' : (1 : ℝ) < a := ha
    have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith)
    have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.1]
    show αpw a b ^ 3 = (1 - b / 2) ^ 3 * (a ^ 3)⁻¹
    unfold αpw
    rw [if_neg c1, if_neg c2, if_pos hb1]
    ring
  have hI3 : ∫ a in Ioi (1 : ℝ), αpw a b ^ 3 = (1 - b / 2) ^ 3 / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEq3, integral_const_mul, integral_Ioi_inv_cube]
    ring
  have hInt3 : IntegrableOn (fun a => αpw a b ^ 3) (Ioi 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul integrableOn_Ioi_inv_cube ((1 - b / 2) ^ 3))
      hEq3.symm measurableSet_Ioi
  -- the part `0 < a ≤ 1` (regions I and II)
  have hb' : 0 ≤ 1 - b := by linarith
  have hi1 : IntervalIntegrable (fun a => αpw a b ^ 3) volume 0 (1 - b) :=
    intervalIntegrable_of_bdd hb' hm 1 (fun a ha => hbd a ⟨ha.1, by linarith [ha.2]⟩)
  have hi2 : IntervalIntegrable (fun a => αpw a b ^ 3) volume (1 - b) 1 :=
    intervalIntegrable_of_bdd (by linarith) hm 1 (fun a ha => hbd a ⟨by linarith [ha.1], ha.2⟩)
  have hInt12 : IntegrableOn (fun a => αpw a b ^ 3) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_of_bdd zero_le_one hm 1 hbd)
  have hI1 : ∫ a in (0 : ℝ)..(1 - b), αpw a b ^ 3 = 1 - b := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · simp
    · intro a ha
      rw [uIcc_of_le hb'] at ha
      have c : a + b ≤ 1 := by linarith [ha.2]
      show αpw a b ^ 3 = 1
      unfold αpw
      rw [if_pos c]
      norm_num
  have hI2 : ∫ a in (1 - b)..1, αpw a b ^ 3 = ∫ s in (0 : ℝ)..b, f2 s b := by
    have e : ∫ a in (1 - b)..1, αpw a b ^ 3 =
        ∫ a in (1 - b)..1, (1 - (a + b - 1) ^ 2 / (2 * a * b)) ^ 3 := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le (by linarith)] at ha
      show αpw a b ^ 3 = (1 - (a + b - 1) ^ 2 / (2 * a * b)) ^ 3
      unfold αpw
      by_cases c : a + b ≤ 1
      · have hab : a + b - 1 = 0 := by linarith [ha.1]
        rw [if_pos c, hab]
        simp
      · rw [ite_eq_right c, if_pos ⟨ha.2, hb1⟩]
    have e2 := intervalIntegral.integral_comp_add_right
      (fun a => (1 - (a + b - 1) ^ 2 / (2 * a * b)) ^ 3) (1 - b) (a := 0) (b := b)
    rw [show (0 : ℝ) + (1 - b) = 1 - b by ring, show b + (1 - b) = 1 by ring] at e2
    rw [e, ← e2]
    apply intervalIntegral.integral_congr
    intro s _
    show (1 - (s + (1 - b) + b - 1) ^ 2 / (2 * (s + (1 - b)) * b)) ^ 3 = f2 s b
    unfold f2
    ring
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union hdisj measurableSet_Ioi hInt12 hInt3, hI3,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hI1, hI2]

lemma inner_large {b : ℝ} (hb : 1 < b) :
    ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 = 17 / 32 * (b ^ 3)⁻¹ := by
  have hEq1 : EqOn (fun a => αpw a b ^ 3) (fun a => (b ^ 3)⁻¹ * (1 - a / 2) ^ 3) (Ioc 0 1) := by
    intro a ha
    have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith [ha.1])
    have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.2]
    have c3 : ¬ (b ≤ 1) := not_le.mpr hb
    show αpw a b ^ 3 = (b ^ 3)⁻¹ * (1 - a / 2) ^ 3
    unfold αpw
    rw [if_neg c1, if_neg c2, if_neg c3, if_pos ha.2]
    ring
  have hEq2 : EqOn (fun a => αpw a b ^ 3) (fun a => (8 * b ^ 3)⁻¹ * (a ^ 3)⁻¹) (Ioi 1) := by
    intro a ha
    have ha' : (1 : ℝ) < a := ha
    have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith)
    have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.2]
    have c3 : ¬ (b ≤ 1) := not_le.mpr hb
    have c4 : ¬ (a ≤ 1) := not_le.mpr ha'
    show αpw a b ^ 3 = (8 * b ^ 3)⁻¹ * (a ^ 3)⁻¹
    unfold αpw
    rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
    ring
  have hInt1 : IntegrableOn (fun a => αpw a b ^ 3) (Ioc 0 1) :=
    (((by fun_prop : Continuous fun a : ℝ => (b ^ 3)⁻¹ * (1 - a / 2) ^ 3).integrableOn_Icc
      (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self).congr_fun hEq1.symm measurableSet_Ioc
  have hInt2 : IntegrableOn (fun a => αpw a b ^ 3) (Ioi 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul integrableOn_Ioi_inv_cube ((8 * b ^ 3)⁻¹))
      hEq2.symm measurableSet_Ioi
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union hdisj measurableSet_Ioi hInt1 hInt2,
    setIntegral_congr_fun measurableSet_Ioc hEq1, setIntegral_congr_fun measurableSet_Ioi hEq2,
    integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_one_sub_half_cube, integral_Ioi_inv_cube]
  ring

/-! ### The flat integral -/

/-- **Lemmas 4.2–4.4**: `∫_{b>0} ∫_{a>0} α(a,b)³ da db = 1 + (13/2 - 5π²/8) = 15/2 - 5π²/8`. -/
theorem flat_integral :
    ∫ b in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 = 15 / 2 - 5 * π ^ 2 / 8 := by
  obtain ⟨hR2int, hswap⟩ := triangle_swap f2 measurable_f2 1 f2_bound
  have hEqA : EqOn (fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3)
      (fun b => (1 - b) + (∫ s in (0 : ℝ)..b, f2 s b) + (1 - b / 2) ^ 3 / 2) (Ioc 0 1) :=
    fun b hb => inner_small hb.1 hb.2
  have hEqB : EqOn (fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3) (fun b => 17 / 32 * (b ^ 3)⁻¹)
      (Ioi 1) :=
    fun b hb => inner_large hb
  have hc1 : IntervalIntegrable (fun b : ℝ => 1 - b) volume 0 1 :=
    (by fun_prop : Continuous fun b : ℝ => 1 - b).intervalIntegrable 0 1
  have hc2 : IntervalIntegrable (fun b : ℝ => (1 - b / 2) ^ 3 / 2) volume 0 1 :=
    (by fun_prop : Continuous fun b : ℝ => (1 - b / 2) ^ 3 / 2).intervalIntegrable 0 1
  have hA : IntegrableOn (fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((hc1.add hR2int).add hc2)).congr_fun hEqA.symm measurableSet_Ioc
  have hB : IntegrableOn (fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3) (Ioi 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul integrableOn_Ioi_inv_cube (17 / 32))
      hEqB.symm measurableSet_Ioi
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
  have hU : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hsplit : ∫ b in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 =
      ∫ b in Ioc 0 1 ∪ Ioi 1, ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 := by
    rw [hU]
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hA hB,
    setIntegral_congr_fun measurableSet_Ioc hEqA, setIntegral_congr_fun measurableSet_Ioi hEqB,
    integral_const_mul, integral_Ioi_inv_cube, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_add (hc1.add hR2int) hc2,
    intervalIntegral.integral_add hc1 hR2int, hswap, regionII, integral_one_sub,
    intervalIntegral.integral_div, integral_one_sub_half_cube]
  ring

end SingularMatrices
