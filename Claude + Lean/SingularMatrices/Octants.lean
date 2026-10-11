import SingularMatrices.SectionArea

/-!
# `α(x)` on the eight octants (Section 4, Lemma 4.1, first half)

For `x ∈ ℝ³` with all coordinates nonzero:

* if all coordinates have the same sign, the plane `x^⊥` meets the cube only at `0`, so
  `areaSec x = 0` (`areaSec_pos`, `areaSec_negs`);
* on the octant `x₀ > 0, x₁ > 0, x₂ < 0`, `areaSec x = αchart x₀ x₁ x₂`, where
  `αchart x₀ x₁ x₂ = √(1 + a² + b²) · αpw a b` with `a = x₀/(-x₂)`, `b = x₁/(-x₂)`
  (`areaSec_chart`);
* `areaSec` is invariant under `x ↦ -x` and under the coordinate swaps `(1 2)` and `(0 2)`.

The other five mixed-sign octants are the images of the first one under these maps. With the
radial cutoff `Frad x = areaSec x ^ 3 · radCut ‖x‖` this gives, for almost every `x`,

  `Frad x = Moct x + Moct (swap12 x) + Moct (swap02 x) + Moct (-x) + Moct (-swap12 x) + Moct (-swap02 x)`

(`Frad_ae`), where `Moct` is `Frad` restricted to the first octant and written by the explicit
formula `αchart`, which is measurable.
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-! ### Measurability of the formulas -/

lemma measurable_αpw2 : Measurable (fun p : ℝ × ℝ => αpw p.1 p.2) := by
  unfold αpw
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
    (Measurable.ite ?_ (by fun_prop)
      (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
        (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
          (by fun_prop))))
  show MeasurableSet ({p : ℝ × ℝ | p.1 ≤ 1} ∩ {p : ℝ × ℝ | p.2 ≤ 1})
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_const)

@[fun_prop]
lemma Measurable.αpw' {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => αpw (f x) (g x) :=
  measurable_αpw2.comp (hf.prodMk hg)

lemma αpw_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ αpw a b := by
  by_cases h : a ≤ 1 ∧ b ≤ 1
  · exact (αpw_mem ha h.1 hb h.2).1
  · unfold αpw
    rw [ite_eq_right (fun h' => h ⟨by linarith, by linarith⟩), ite_eq_right h]
    split_ifs with h1 h2
    · exact div_nonneg (by linarith) ha.le
    · exact div_nonneg (by linarith) hb.le
    · exact (div_pos one_pos (mul_pos (mul_pos two_pos ha) hb)).le

/-- `α` in the chart over the octant `x₀ > 0, x₁ > 0, x₂ < 0`. -/
noncomputable def αchart (x0 x1 x2 : ℝ) : ℝ :=
  √(1 + (x0 / -x2) ^ 2 + (x1 / -x2) ^ 2) * αpw (x0 / -x2) (x1 / -x2)

@[fun_prop]
lemma Measurable.αchart' {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable fun x => αchart (f x) (g x) (h x) := by
  unfold αchart
  have h1 : Measurable fun x => f x / -h x := hf.div hh.neg
  have h2 : Measurable fun x => g x / -h x := hg.div hh.neg
  exact (Real.continuous_sqrt.measurable.comp
    ((measurable_const.add (h1.pow_const 2)).add (h2.pow_const 2))).mul (Measurable.αpw' h1 h2)

/-- The integrand on the first octant, inside the unit ball, as an explicit formula. -/
noncomputable def Moctc (x0 x1 x2 : ℝ) : ℝ :=
  if 0 < x0 ∧ 0 < x1 ∧ x2 < 0 ∧ x0 ^ 2 + x1 ^ 2 + x2 ^ 2 < 1 then 3 * αchart x0 x1 x2 ^ 3
  else 0

@[fun_prop]
lemma Measurable.Moctc' {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable fun x => Moctc (f x) (g x) (h x) := by
  unfold Moctc
  refine Measurable.ite ?_ (((Measurable.αchart' hf hg hh).pow_const 3).const_mul 3)
    measurable_const
  show MeasurableSet ({x | 0 < f x} ∩ ({x | 0 < g x} ∩ ({x | h x < 0} ∩
    {x | f x ^ 2 + g x ^ 2 + h x ^ 2 < 1})))
  exact (measurableSet_lt measurable_const hf).inter ((measurableSet_lt measurable_const hg).inter
    ((measurableSet_lt hh measurable_const).inter
      (measurableSet_lt (((hf.pow_const 2).add (hg.pow_const 2)).add (hh.pow_const 2))
        measurable_const)))

lemma measurable_coord (i : Fin 3) : Measurable (fun x : E3 => x.ofLp i) := by
  have h : Measurable (fun x : E3 => (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x i) :=
    (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurable
  simpa only [MeasurableEquiv.toLp_symm_apply] using h

/-- `Moct x`: the explicit integrand on the first octant. -/
noncomputable def Moct (x : E3) : ℝ := Moctc (x.ofLp 0) (x.ofLp 1) (x.ofLp 2)

lemma measurable_Moct_comp {L : E3 → E3} (hL : Measurable L) :
    Measurable (fun x => Moct (L x)) :=
  Measurable.Moctc' ((measurable_coord 0).comp hL) ((measurable_coord 1).comp hL)
    ((measurable_coord 2).comp hL)

lemma Moct_nonneg (x : E3) : 0 ≤ Moct x := by
  unfold Moct Moctc αchart
  split_ifs with h
  · have ht : 0 < -x.ofLp 2 := neg_pos.mpr h.2.2.1
    exact mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (αpw_nonneg (div_pos h.1 ht) (div_pos h.2.1 ht))) 3)
  · exact le_refl 0

/-! ### `α` on the first octant -/

lemma areaSec_chart {x : E3} (h0 : 0 < x.ofLp 0) (h1 : 0 < x.ofLp 1) (h2 : x.ofLp 2 < 0) :
    areaSec x = αchart (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) := by
  have ht : 0 < -x.ofLp 2 := neg_pos.mpr h2
  have e : (-x.ofLp 2)⁻¹ • x = wvec (x.ofLp 0 / -x.ofLp 2) (x.ofLp 1 / -x.ofLp 2) := by
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · show (-x.ofLp 2)⁻¹ * x.ofLp 0 = x.ofLp 0 / -x.ofLp 2
      ring
    · show (-x.ofLp 2)⁻¹ * x.ofLp 1 = x.ofLp 1 / -x.ofLp 2
      ring
    · show (-x.ofLp 2)⁻¹ * x.ofLp 2 = -1
      rw [inv_mul_eq_iff_eq_mul₀ ht.ne']
      ring
  rw [← areaSec_smul (inv_ne_zero ht.ne'), e, areaSec_wvec (div_pos h0 ht) (div_pos h1 ht)]
  rfl

/-! ### Same-sign octants: the section is `{0}` -/

lemma hE2_singleton (y : E3) : Measure.euclideanHausdorffMeasure 2 ({y} : Set E3) = 0 := by
  rcases Measure.euclideanHausdorffMeasure_zero_or_top (d₁ := 0) (d₂ := 2) (by norm_num)
    ({y} : Set E3) with h | h
  · exact h
  · simp [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton] at h

lemma areaSec_pos {v : E3} (h0 : 0 < v.ofLp 0) (h1 : 0 < v.ofLp 1) (h2 : 0 < v.ofLp 2) :
    areaSec v = 0 := by
  have hsub : sec v ⊆ {0} := by
    rintro x ⟨hx, hc⟩
    have hx' : v.ofLp 0 * x.ofLp 0 + v.ofLp 1 * x.ofLp 1 + v.ofLp 2 * x.ofLp 2 = 0 := by
      rw [← inner_E3]
      exact hx
    obtain ⟨⟨a0, _⟩, ⟨a1, _⟩, ⟨a2, _⟩⟩ := mem_cube.mp hc
    have p0 := mul_nonneg h0.le a0
    have p1 := mul_nonneg h1.le a1
    have p2 := mul_nonneg h2.le a2
    have e0 : x.ofLp 0 = 0 :=
      (mul_eq_zero.mp (by linarith : v.ofLp 0 * x.ofLp 0 = 0)).resolve_left h0.ne'
    have e1 : x.ofLp 1 = 0 :=
      (mul_eq_zero.mp (by linarith : v.ofLp 1 * x.ofLp 1 = 0)).resolve_left h1.ne'
    have e2 : x.ofLp 2 = 0 :=
      (mul_eq_zero.mp (by linarith : v.ofLp 2 * x.ofLp 2 = 0)).resolve_left h2.ne'
    show x = 0
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e0, e1, e2]
  unfold areaSec
  rw [measure_mono_null hsub (hE2_singleton 0), ENNReal.toReal_zero]

lemma neg_ofLp (v : E3) (i : Fin 3) : (-v).ofLp i = -v.ofLp i := by
  rfl

lemma areaSec_neg (v : E3) : areaSec (-v) = areaSec v := by
  rw [← neg_one_smul ℝ v, areaSec_smul (by norm_num)]

lemma areaSec_negs {v : E3} (h0 : v.ofLp 0 < 0) (h1 : v.ofLp 1 < 0) (h2 : v.ofLp 2 < 0) :
    areaSec v = 0 := by
  rw [← areaSec_neg]
  exact areaSec_pos (by rw [neg_ofLp]; linarith) (by rw [neg_ofLp]; linarith)
    (by rw [neg_ofLp]; linarith)

/-! ### Coordinate swaps -/

/-- An isometry of `ℝ³` preserving the cube preserves `α`. -/
lemma areaSec_isom (L : E3 ≃ₗᵢ[ℝ] E3) (hL : ∀ y, L y ∈ cube ↔ y ∈ cube) (v : E3) :
    areaSec (L v) = areaSec v := by
  have hs : sec (L v) = L '' sec v := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨L.symm x, ⟨?_, ?_⟩, L.apply_symm_apply x⟩
      · show inner ℝ v (L.symm x) = 0
        rw [← L.inner_map_map, L.apply_symm_apply]
        exact h1
      · rw [← hL, L.apply_symm_apply]
        exact h2
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, (hL y).mpr h2⟩
      show inner ℝ (L v) (L y) = 0
      rw [L.inner_map_map]
      exact h1
  unfold areaSec
  rw [hs, L.isometry.euclideanHausdorffMeasure_image]

/-- The swap of coordinates `1` and `2`. -/
noncomputable def swap12 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1 : Fin 3) 2)

/-- The swap of coordinates `0` and `2`. -/
noncomputable def swap02 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 2)

lemma swap12_apply (v : E3) (i : Fin 3) : (swap12 v).ofLp i = v.ofLp (Equiv.swap 1 2 i) := by
  simp [swap12, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

lemma swap02_apply (v : E3) (i : Fin 3) : (swap02 v).ofLp i = v.ofLp (Equiv.swap 0 2 i) := by
  simp [swap02, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

lemma swap12_0 (v : E3) : (swap12 v).ofLp 0 = v.ofLp 0 := by
  rw [swap12_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
lemma swap12_1 (v : E3) : (swap12 v).ofLp 1 = v.ofLp 2 := by
  rw [swap12_apply, Equiv.swap_apply_left]
lemma swap12_2 (v : E3) : (swap12 v).ofLp 2 = v.ofLp 1 := by
  rw [swap12_apply, Equiv.swap_apply_right]
lemma swap02_0 (v : E3) : (swap02 v).ofLp 0 = v.ofLp 2 := by
  rw [swap02_apply, Equiv.swap_apply_left]
lemma swap02_1 (v : E3) : (swap02 v).ofLp 1 = v.ofLp 1 := by
  rw [swap02_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
lemma swap02_2 (v : E3) : (swap02 v).ofLp 2 = v.ofLp 0 := by
  rw [swap02_apply, Equiv.swap_apply_right]

lemma swap12_cube (y : E3) : swap12 y ∈ cube ↔ y ∈ cube := by
  rw [mem_cube, mem_cube, swap12_0, swap12_1, swap12_2]
  tauto

lemma swap02_cube (y : E3) : swap02 y ∈ cube ↔ y ∈ cube := by
  rw [mem_cube, mem_cube, swap02_0, swap02_1, swap02_2]
  tauto

lemma areaSec_swap12 (v : E3) : areaSec (swap12 v) = areaSec v :=
  areaSec_isom swap12 swap12_cube v

lemma areaSec_swap02 (v : E3) : areaSec (swap02 v) = areaSec v :=
  areaSec_isom swap02 swap02_cube v

/-! ### The radial integrand and its decomposition -/

/-- The radial weight: `3` on the open unit ball, `0` outside; `∫₀^∞ radCut r · r² dr = 1`. -/
noncomputable def radCut (r : ℝ) : ℝ := if r < 1 then 3 else 0

/-- `α(x)³` cut off radially. -/
noncomputable def Frad (x : E3) : ℝ := areaSec x ^ 3 * radCut ‖x‖

lemma Frad_nonneg (x : E3) : 0 ≤ Frad x := by
  have h0 : 0 ≤ areaSec x := ENNReal.toReal_nonneg
  unfold Frad radCut
  split_ifs
  · exact mul_nonneg (pow_nonneg h0 3) (by norm_num)
  · simp

lemma Frad_neg (v : E3) : Frad (-v) = Frad v := by
  unfold Frad
  rw [areaSec_neg, norm_neg]

lemma Frad_swap12 (v : E3) : Frad (swap12 v) = Frad v := by
  unfold Frad
  rw [areaSec_swap12, LinearIsometryEquiv.norm_map]

lemma Frad_swap02 (v : E3) : Frad (swap02 v) = Frad v := by
  unfold Frad
  rw [areaSec_swap02, LinearIsometryEquiv.norm_map]

lemma normsq_E3 (x : E3) : ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_E3]
  ring

lemma norm_lt_one_iff_E3 (x : E3) :
    ‖x‖ < 1 ↔ x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 < 1 := by
  rw [← normsq_E3]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    by_contra h'
    push Not at h'
    nlinarith [norm_nonneg x]

lemma Moct_eq_Frad {y : E3} (h0 : 0 < y.ofLp 0) (h1 : 0 < y.ofLp 1) (h2 : y.ofLp 2 < 0) :
    Moct y = Frad y := by
  unfold Moct Moctc Frad radCut
  rw [areaSec_chart h0 h1 h2]
  by_cases hn : ‖y‖ < 1
  · rw [ite_eq_left ⟨h0, h1, h2, (norm_lt_one_iff_E3 y).mp hn⟩, ite_eq_left hn]
    ring
  · rw [ite_eq_right (fun h => hn ((norm_lt_one_iff_E3 y).mpr h.2.2.2)), ite_eq_right hn]
    ring

lemma Moct_eq_zero {y : E3} (h : ¬ (0 < y.ofLp 0 ∧ 0 < y.ofLp 1 ∧ y.ofLp 2 < 0)) :
    Moct y = 0 := by
  unfold Moct Moctc
  rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]

lemma Moct_of_Frad {w y : E3} (h : Frad w = Frad y) :
    Moct w = if 0 < w.ofLp 0 ∧ 0 < w.ofLp 1 ∧ w.ofLp 2 < 0 then Frad y else 0 := by
  split_ifs with hc
  · rw [Moct_eq_Frad hc.1 hc.2.1 hc.2.2, h]
  · exact Moct_eq_zero hc

lemma Frad_pos {x : E3} (h0 : 0 < x.ofLp 0) (h1 : 0 < x.ofLp 1) (h2 : 0 < x.ofLp 2) :
    Frad x = 0 := by
  unfold Frad
  rw [areaSec_pos h0 h1 h2]
  ring

lemma Frad_negs {x : E3} (h0 : x.ofLp 0 < 0) (h1 : x.ofLp 1 < 0) (h2 : x.ofLp 2 < 0) :
    Frad x = 0 := by
  unfold Frad
  rw [areaSec_negs h0 h1 h2]
  ring

lemma sign_cases {a : ℝ} (h : a ≠ 0) : (0 < a ∧ ¬ a < 0) ∨ (a < 0 ∧ ¬ 0 < a) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact Or.inr ⟨h', not_lt.mpr h'.le⟩
  · exact Or.inl ⟨h', not_lt.mpr h'.le⟩

/-- Off the coordinate planes, `Frad` is the sum of the six octant pieces. -/
lemma Frad_decomp {x : E3} (h0 : x.ofLp 0 ≠ 0) (h1 : x.ofLp 1 ≠ 0) (h2 : x.ofLp 2 ≠ 0) :
    Frad x = Moct x + Moct (swap12 x) + Moct (swap02 x) + Moct (-x) + Moct (-(swap12 x)) +
      Moct (-(swap02 x)) := by
  rw [Moct_of_Frad (rfl : Frad x = Frad x), Moct_of_Frad (Frad_swap12 x),
    Moct_of_Frad (Frad_swap02 x), Moct_of_Frad (Frad_neg x),
    Moct_of_Frad ((Frad_neg _).trans (Frad_swap12 x)),
    Moct_of_Frad ((Frad_neg _).trans (Frad_swap02 x))]
  simp only [swap12_0, swap12_1, swap12_2, swap02_0, swap02_1, swap02_2, neg_ofLp]
  rcases sign_cases h0 with ⟨p0, n0⟩ | ⟨p0, n0⟩ <;>
  rcases sign_cases h1 with ⟨p1, n1⟩ | ⟨p1, n1⟩ <;>
  rcases sign_cases h2 with ⟨p2, n2⟩ | ⟨p2, n2⟩
  all_goals first
    | (simp [p0, p1, p2, n0, n1, n2]; done)
    | (rw [Frad_pos p0 p1 p2]; simp)
    | (rw [Frad_negs p0 p1 p2]; simp)

/-! ### Coordinate planes are null -/

lemma null_coord (i : Fin 3) : volume {x : E3 | x.ofLp i = 0} = 0 := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((measurableSet_singleton (0 : ℝ)).preimage
      (measurable_pi_apply i : Measurable fun y : Fin 3 → ℝ => y i)).nullMeasurableSet
  have h2 : (volume : Measure (Fin 3 → ℝ)) {y | y i = 0} = 0 :=
    Measure.pi_hyperplane (fun _ => volume) i 0
  exact h.trans h2

lemma ae_coord_ne (i : Fin 3) : ∀ᵐ x : E3, x.ofLp i ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using null_coord i

lemma Frad_ae : ∀ᵐ x : E3, Frad x = Moct x + Moct (swap12 x) + Moct (swap02 x) + Moct (-x) +
    Moct (-(swap12 x)) + Moct (-(swap02 x)) := by
  filter_upwards [ae_coord_ne 0, ae_coord_ne 1, ae_coord_ne 2] with x h0 h1 h2
  exact Frad_decomp h0 h1 h2

end SingularMatrices
