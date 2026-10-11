import SingularMatrices.Octants

/-!
# The integral over one octant (Section 4, Lemma 4.1, second half)

* `octant_lintegral`: `∫⁻_{ℝ³} Moct = 15/2 - 5π²/8`.

`Moct` is `3 α(x)³` on `{x₀ > 0, x₁ > 0, x₂ < 0, |x| < 1}` and `0` elsewhere. Write `t = -x₂ > 0`
and `(x₀, x₁) = t (a, b)`. For fixed `x₂` the linear substitution `(x₀, x₁) = t (a, b)` has
Jacobian `t²` (`inner_scale`). Exchanging the order of integration (Tonelli), the integral over
`x₂` is `∫ t² dt` over `0 < t < 1/√q`, `q = 1 + a² + b²`, which equals `q^{-3/2}/3`; since
`α = √q · αpw a b` on the octant, this leaves `αpw a b ³` (`t_integral`). What remains is the flat
integral `∫∫ αpw³ = 15/2 - 5π²/8` (`flat_integral`), written as a Lebesgue integral
(`flat_lintegral`).
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-! ### The flat integral as a Lebesgue integral -/

lemma integrableOn_inner {b : ℝ} (hb : 0 < b) : IntegrableOn (fun a => αpw a b ^ 3) (Ioi 0) := by
  have hU : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hU]
  rcases le_or_gt b 1 with hb1 | hb1
  · have hm : Measurable (fun a => αpw a b ^ 3) := (measurable_αpw b).pow_const 3
    have hbd : ∀ a ∈ Ioc (0 : ℝ) 1, |αpw a b ^ 3| ≤ 1 := fun a ha => by
      obtain ⟨h0, h1⟩ := αpw_mem ha.1 ha.2 hb hb1
      rw [abs_of_nonneg (pow_nonneg h0 3)]
      exact pow_le_one₀ h0 h1
    have hEq3 : EqOn (fun a => αpw a b ^ 3) (fun a => (1 - b / 2) ^ 3 * (a ^ 3)⁻¹) (Ioi 1) := by
      intro a ha
      have ha' : (1 : ℝ) < a := ha
      have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith)
      have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.1]
      show αpw a b ^ 3 = (1 - b / 2) ^ 3 * (a ^ 3)⁻¹
      unfold αpw
      rw [ite_eq_right c1, ite_eq_right c2, ite_eq_left hb1]
      ring
    have hInt3 : IntegrableOn (fun a => αpw a b ^ 3) (Ioi 1) :=
      IntegrableOn.congr_fun (Integrable.const_mul integrableOn_Ioi_inv_cube ((1 - b / 2) ^ 3))
        hEq3.symm measurableSet_Ioi
    have hInt12 : IntegrableOn (fun a => αpw a b ^ 3) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_of_bdd zero_le_one hm 1 hbd)
    exact hInt12.union hInt3
  · have hEq1 : EqOn (fun a => αpw a b ^ 3) (fun a => (b ^ 3)⁻¹ * (1 - a / 2) ^ 3)
        (Ioc 0 1) := by
      intro a ha
      have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith [ha.1])
      have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.2]
      have c3 : ¬ (b ≤ 1) := not_le.mpr hb1
      show αpw a b ^ 3 = (b ^ 3)⁻¹ * (1 - a / 2) ^ 3
      unfold αpw
      rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_left ha.2]
      ring
    have hEq2 : EqOn (fun a => αpw a b ^ 3) (fun a => (8 * b ^ 3)⁻¹ * (a ^ 3)⁻¹) (Ioi 1) := by
      intro a ha
      have ha' : (1 : ℝ) < a := ha
      have c1 : ¬ (a + b ≤ 1) := not_le.mpr (by linarith)
      have c2 : ¬ (a ≤ 1 ∧ b ≤ 1) := fun h => by linarith [h.2]
      have c3 : ¬ (b ≤ 1) := not_le.mpr hb1
      have c4 : ¬ (a ≤ 1) := not_le.mpr ha'
      show αpw a b ^ 3 = (8 * b ^ 3)⁻¹ * (a ^ 3)⁻¹
      unfold αpw
      rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4]
      ring
    have hInt1 : IntegrableOn (fun a => αpw a b ^ 3) (Ioc 0 1) :=
      (((by fun_prop : Continuous fun a : ℝ => (b ^ 3)⁻¹ * (1 - a / 2) ^ 3).integrableOn_Icc
        (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self).congr_fun hEq1.symm measurableSet_Ioc
    have hInt2 : IntegrableOn (fun a => αpw a b ^ 3) (Ioi 1) :=
      IntegrableOn.congr_fun (Integrable.const_mul integrableOn_Ioi_inv_cube ((8 * b ^ 3)⁻¹))
        hEq2.symm measurableSet_Ioi
    exact hInt1.union hInt2

lemma integrableOn_outer :
    IntegrableOn (fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3) (Ioi 0) := by
  obtain ⟨hR2int, _⟩ := triangle_swap f2 measurable_f2 1 f2_bound
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
  have h := hA.union hB
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- `∫⁻_{b>0} ∫⁻_{a>0} αpw(a,b)³ = 15/2 - 5π²/8`. -/
lemma flat_lintegral :
    ∫⁻ b in Ioi (0 : ℝ), ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3) =
      ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by
  have hinner : EqOn (fun b => ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3))
      (fun b => ENNReal.ofReal (∫ a in Ioi (0 : ℝ), αpw a b ^ 3)) (Ioi 0) := by
    intro b hb
    exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_inner hb)
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun a ha => pow_nonneg (αpw_nonneg ha hb) 3))).symm
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun b => ∫ a in Ioi (0 : ℝ), αpw a b ^ 3 :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun b hb =>
      setIntegral_nonneg measurableSet_Ioi (fun a ha => pow_nonneg (αpw_nonneg ha hb) 3))
  calc ∫⁻ b in Ioi (0 : ℝ), ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3)
      = ∫⁻ b in Ioi (0 : ℝ), ENNReal.ofReal (∫ a in Ioi (0 : ℝ), αpw a b ^ 3) :=
        setLIntegral_congr_fun measurableSet_Ioi hinner
    _ = ENNReal.ofReal (∫ b in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), αpw a b ^ 3) :=
        (ofReal_integral_eq_lintegral_ofReal integrableOn_outer hnn).symm
    _ = ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by rw [flat_integral]

/-- `αpw(a,b)³` on the open quarter plane, `0` elsewhere. -/
noncomputable def Gflat (a b : ℝ) : ENNReal :=
  if 0 < a ∧ 0 < b then ENNReal.ofReal (αpw a b ^ 3) else 0

lemma measurable_Gflat : Measurable (fun p : ℝ × ℝ => Gflat p.1 p.2) := by
  unfold Gflat
  refine Measurable.ite ?_ ?_ measurable_const
  · show MeasurableSet ({p : ℝ × ℝ | 0 < p.1} ∩ {p : ℝ × ℝ | 0 < p.2})
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact ENNReal.measurable_ofReal.comp
      ((Measurable.αpw' measurable_fst measurable_snd).pow_const 3)

lemma lintegral_Gflat :
    ∫⁻ w : Fin 2 → ℝ, Gflat (w 0) (w 1) = ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by
  have h4 := (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun p : ℝ × ℝ => Gflat p.1 p.2)
  have hF0 : ∀ b : ℝ, ∫⁻ a : ℝ, Gflat a b =
      (Ioi (0 : ℝ)).indicator (fun x : ℝ => ∫⁻ a : ℝ, Gflat a x) b := by
    intro b
    by_cases hb : (0 : ℝ) < b
    · rw [Set.indicator_of_mem (show b ∈ Ioi (0 : ℝ) from hb)]
    · rw [Set.indicator_of_notMem (show b ∉ Ioi (0 : ℝ) from hb)]
      have h0 : ∀ a : ℝ, Gflat a b = 0 := fun a => by
        unfold Gflat
        rw [ite_eq_right (fun h => hb h.2)]
      simp only [h0, lintegral_zero]
  have hF1 : EqOn (fun b => ∫⁻ a : ℝ, Gflat a b)
      (fun b => ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3)) (Ioi 0) := by
    intro b hb
    show ∫⁻ a : ℝ, Gflat a b = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3)
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr (fun a => ?_)
    unfold Gflat
    by_cases ha : (0 : ℝ) < a
    · rw [ite_eq_left ⟨ha, hb⟩, indicator_of_mem (show a ∈ Ioi (0 : ℝ) from ha)]
    · rw [ite_eq_right (fun h => ha h.1), indicator_of_notMem (show a ∉ Ioi (0 : ℝ) from ha)]
  calc
    ∫⁻ w : Fin 2 → ℝ, Gflat (w 0) (w 1)
        = ∫⁻ p : ℝ × ℝ, Gflat p.1 p.2 := by
          exact h4
    _ = ∫⁻ b : ℝ, ∫⁻ a : ℝ, Gflat a b := by
          rw [Measure.volume_eq_prod]
          exact lintegral_prod_symm (fun p : ℝ × ℝ => Gflat p.1 p.2)
            measurable_Gflat.aemeasurable
    _ = ∫⁻ b : ℝ, (Ioi (0 : ℝ)).indicator (fun x : ℝ => ∫⁻ a : ℝ, Gflat a x) b := by
          exact lintegral_congr hF0
    _ = ∫⁻ b in Ioi (0 : ℝ), ∫⁻ a : ℝ, Gflat a b := by
          rw [lintegral_indicator measurableSet_Ioi]
    _ = ∫⁻ b in Ioi (0 : ℝ), ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (αpw a b ^ 3) := by
          refine setLIntegral_congr_fun measurableSet_Ioi ?_
          exact hF1
    _ = ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := flat_lintegral

/-! ### The substitution `(x₀, x₁) = t (a, b)` -/

lemma inner_scale (x2 : ℝ) :
    ∫⁻ v : Fin 2 → ℝ, ENNReal.ofReal (Moctc (v 0) (v 1) x2) =
      ∫⁻ w : Fin 2 → ℝ, ENNReal.ofReal (x2 ^ 2) *
        ENNReal.ofReal (Moctc (-x2 * w 0) (-x2 * w 1) x2) := by
  rcases lt_or_ge x2 0 with hx | hx
  · have hr : (-x2) ≠ 0 := neg_ne_zero.mpr hx.ne
    have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 2 → ℝ)) hr
    rw [Module.finrank_fin_fun] at hmap
    have hk : Measurable (fun v : Fin 2 → ℝ => ENNReal.ofReal (Moctc (v 0) (v 1) x2)) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.Moctc' (measurable_pi_apply 0) (measurable_pi_apply 1) measurable_const)
    have hg : Measurable (fun w : Fin 2 → ℝ => (-x2) • w) :=
      (continuous_const_smul (-x2)).measurable
    have h1 : ∫⁻ w : Fin 2 → ℝ, ENNReal.ofReal (Moctc (-x2 * w 0) (-x2 * w 1) x2) =
        ENNReal.ofReal |((-x2) ^ 2)⁻¹| *
          ∫⁻ v : Fin 2 → ℝ, ENNReal.ofReal (Moctc (v 0) (v 1) x2) := by
      have h := lintegral_map hk hg (μ := (volume : Measure (Fin 2 → ℝ)))
      rw [hmap, lintegral_smul_measure, smul_eq_mul] at h
      exact h.symm
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg x2)]
    have h2 : x2 ^ 2 * |((-x2) ^ 2)⁻¹| = 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), neg_sq]
      exact mul_inv_cancel₀ (pow_ne_zero 2 hx.ne)
    rw [h2, ENNReal.ofReal_one, one_mul]
  · have h0 : ∀ y0 y1 : ℝ, Moctc y0 y1 x2 = 0 := fun y0 y1 => by
      unfold Moctc
      rw [ite_eq_right]
      rintro ⟨_, _, h, _⟩
      linarith
    simp only [h0, ENNReal.ofReal_zero, mul_zero, lintegral_zero]

/-! ### The integral over `t = -x₂` -/

lemma t_integral (a b : ℝ) :
    ∫⁻ x2 : ℝ, ENNReal.ofReal (x2 ^ 2) * ENNReal.ofReal (Moctc (-x2 * a) (-x2 * b) x2) =
      Gflat a b := by
  unfold Gflat
  split_ifs with hab
  · obtain ⟨ha, hb⟩ := hab
    have hq0 : 0 < 1 + a ^ 2 + b ^ 2 := by positivity
    have hsq : 0 < √(1 + a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hq0
    have hsq2 : √(1 + a ^ 2 + b ^ 2) ^ 2 = 1 + a ^ 2 + b ^ 2 := Real.sq_sqrt hq0.le
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / √(1 + a ^ 2 + b ^ 2) := ⟨_, rfl⟩
    have hr0 : 0 < r := by rw [hr]; positivity
    have hrq : r * √(1 + a ^ 2 + b ^ 2) = 1 := by rw [hr]; exact one_div_mul_cancel hsq.ne'
    have key : ∀ x2 : ℝ, x2 < 0 →
        ((-x2 * a) ^ 2 + (-x2 * b) ^ 2 + x2 ^ 2 < 1 ↔ -r < x2) := by
      intro x2 hx2
      have hs : 0 < -x2 := neg_pos.mpr hx2
      have hid : (-x2 * a) ^ 2 + (-x2 * b) ^ 2 + x2 ^ 2 = (-x2 * √(1 + a ^ 2 + b ^ 2)) ^ 2 := by
        calc
          (-x2 * a) ^ 2 + (-x2 * b) ^ 2 + x2 ^ 2
              = (-x2) ^ 2 * a ^ 2 + (-x2) ^ 2 * b ^ 2 + x2 ^ 2 := by ring
          _ = (-x2) ^ 2 * (1 + a ^ 2 + b ^ 2) := by ring
          _ = (-x2) ^ 2 * (√(1 + a ^ 2 + b ^ 2)) ^ 2 := by rw [hsq2]
          _ = (-x2 * √(1 + a ^ 2 + b ^ 2)) ^ 2 := by ring
      have hpos : 0 < -x2 * √(1 + a ^ 2 + b ^ 2) := mul_pos hs hsq
      constructor
      · intro h
        have h1 : -x2 * √(1 + a ^ 2 + b ^ 2) < 1 := by nlinarith
        by_contra hc
        push Not at hc
        have : r * √(1 + a ^ 2 + b ^ 2) ≤ -x2 * √(1 + a ^ 2 + b ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hsq.le
        linarith
      · intro h
        have h1 : -x2 * √(1 + a ^ 2 + b ^ 2) < 1 := by
          have : -x2 * √(1 + a ^ 2 + b ^ 2) < r * √(1 + a ^ 2 + b ^ 2) :=
            mul_lt_mul_of_pos_right (by linarith) hsq
          linarith
        nlinarith
    have hpt : ∀ x2 : ℝ, ENNReal.ofReal (x2 ^ 2) * ENNReal.ofReal (Moctc (-x2 * a) (-x2 * b) x2) =
        (Ioo (-r) 0).indicator (fun x2 => ENNReal.ofReal (3 * (√(1 + a ^ 2 + b ^ 2) * αpw a b) ^ 3) *
          ENNReal.ofReal (x2 ^ 2)) x2 := by
      intro x2
      by_cases hx : x2 ∈ Ioo (-r) 0
      · rw [indicator_of_mem hx]
        have hx2 : x2 < 0 := hx.2
        have hs : 0 < -x2 := neg_pos.mpr hx2
        have hM : Moctc (-x2 * a) (-x2 * b) x2 = 3 * (√(1 + a ^ 2 + b ^ 2) * αpw a b) ^ 3 := by
          unfold Moctc
          rw [ite_eq_left ⟨mul_pos hs ha, mul_pos hs hb, hx2, (key x2 hx2).mpr hx.1⟩]
          unfold αchart
          rw [mul_div_cancel_left₀ a hs.ne', mul_div_cancel_left₀ b hs.ne']
        rw [hM]
        exact mul_comm _ _
      · rw [indicator_of_notMem hx]
        have hM : Moctc (-x2 * a) (-x2 * b) x2 = 0 := by
          unfold Moctc
          rw [ite_eq_right]
          rintro ⟨_, _, h2, h3⟩
          exact hx ⟨(key x2 h2).mp h3, h2⟩
        rw [hM, ENNReal.ofReal_zero, mul_zero]
    have hm2 : Measurable (fun x2 : ℝ => ENNReal.ofReal (x2 ^ 2)) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
    have hI : ∫⁻ x2 in Ioo (-r) 0, ENNReal.ofReal (x2 ^ 2) = ENNReal.ofReal (r ^ 3 / 3) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (((continuous_pow 2 : Continuous fun x : ℝ => x ^ 2).integrableOn_Icc).mono_set
          Ioo_subset_Icc_self)
        (Filter.Eventually.of_forall (fun x => sq_nonneg x))]
      congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
        integral_pow]
      simp only [Nat.cast_ofNat]
      ring
    have hc0 : 0 ≤ 3 * (√(1 + a ^ 2 + b ^ 2) * αpw a b) ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (αpw_nonneg ha hb)) 3)
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ hm2, hI,
      ← ENNReal.ofReal_mul hc0]
    congr 1
    have e : 3 * (√(1 + a ^ 2 + b ^ 2) * αpw a b) ^ 3 * (r ^ 3 / 3) =
        αpw a b ^ 3 * (r * √(1 + a ^ 2 + b ^ 2)) ^ 3 := by ring
    rw [e, hrq]
    ring
  · have h0 : ∀ x2 : ℝ, Moctc (-x2 * a) (-x2 * b) x2 = 0 := by
      intro x2
      unfold Moctc
      rw [ite_eq_right]
      rintro ⟨h1, h2, h3, _⟩
      have hs : 0 < -x2 := neg_pos.mpr h3
      exact hab ⟨pos_of_mul_pos_right h1 hs.le, pos_of_mul_pos_right h2 hs.le⟩
    simp only [h0, ENNReal.ofReal_zero, mul_zero, lintegral_zero]

/-! ### Assembly -/

/-- **The octant integral**: `∫⁻_{ℝ³} Moct = 15/2 - 5π²/8`. -/
theorem octant_lintegral :
    ∫⁻ x : E3, ENNReal.ofReal (Moct x) = ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by
  have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → (Fin 3 → ℝ)) := by
    rw [← MeasurableEquiv.coe_toLp_symm]
    exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have e1 : ∫⁻ x : E3, ENNReal.ofReal (Moct x) =
      ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (Moctc (y 0) (y 1) (y 2)) :=
    (PiLp.volume_preserving_ofLp (Fin 3)).lintegral_comp_emb hemb
      (fun y : Fin 3 → ℝ => ENNReal.ofReal (Moctc (y 0) (y 1) (y 2)))
  have e2 : ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (Moctc (y 0) (y 1) (y 2)) =
      ∫⁻ p : ℝ × (Fin 2 → ℝ), ENNReal.ofReal (Moctc (p.2 0) (p.2 1) p.1) := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).lintegral_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).measurableEmbedding
      (fun p : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal (Moctc (p.2 0) (p.2 1) p.1))
    rw [← h]
    refine lintegral_congr (fun y => ?_)
    -- the coordinates of `piFinSuccAbove _ 2 y = (y 2, (y 0, y 1))`
    have c1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2 y).1 = y 2 := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    have c2 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2 y).2 0 = y 0 := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
      all_goals rfl
    have c3 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2 y).2 1 = y 1 := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
      all_goals rfl
    simp only [c1, c2, c3]
  have hp0 : Measurable (fun p : ℝ × (Fin 2 → ℝ) => p.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have hp1 : Measurable (fun p : ℝ × (Fin 2 → ℝ) => p.2 1) :=
    (measurable_pi_apply 1).comp measurable_snd
  have hg3 : Measurable (fun p : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal (Moctc (p.2 0) (p.2 1) p.1)) :=
    ENNReal.measurable_ofReal.comp (Measurable.Moctc' hp0 hp1 measurable_fst)
  have e3 : ∫⁻ p : ℝ × (Fin 2 → ℝ), ENNReal.ofReal (Moctc (p.2 0) (p.2 1) p.1) =
      ∫⁻ x2 : ℝ, ∫⁻ v : Fin 2 → ℝ, ENNReal.ofReal (Moctc (v 0) (v 1) x2) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ hg3.aemeasurable
  have hsw : AEMeasurable (Function.uncurry fun (x2 : ℝ) (w : Fin 2 → ℝ) =>
      ENNReal.ofReal (x2 ^ 2) * ENNReal.ofReal (Moctc (-x2 * w 0) (-x2 * w 1) x2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (show Measurable (fun p : ℝ × (Fin 2 → ℝ) =>
        ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (Moctc (-p.1 * p.2 0) (-p.1 * p.2 1) p.1)) from
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2)).mul
        (ENNReal.measurable_ofReal.comp (Measurable.Moctc' (measurable_fst.neg.mul hp0)
          (measurable_fst.neg.mul hp1) measurable_fst))).aemeasurable
  calc ∫⁻ x : E3, ENNReal.ofReal (Moct x)
      = ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (Moctc (y 0) (y 1) (y 2)) := e1
    _ = ∫⁻ p : ℝ × (Fin 2 → ℝ), ENNReal.ofReal (Moctc (p.2 0) (p.2 1) p.1) := e2
    _ = ∫⁻ x2 : ℝ, ∫⁻ v : Fin 2 → ℝ, ENNReal.ofReal (Moctc (v 0) (v 1) x2) := e3
    _ = ∫⁻ x2 : ℝ, ∫⁻ w : Fin 2 → ℝ, ENNReal.ofReal (x2 ^ 2) *
          ENNReal.ofReal (Moctc (-x2 * w 0) (-x2 * w 1) x2) := lintegral_congr inner_scale
    _ = ∫⁻ w : Fin 2 → ℝ, ∫⁻ x2 : ℝ, ENNReal.ofReal (x2 ^ 2) *
          ENNReal.ofReal (Moctc (-x2 * w 0) (-x2 * w 1) x2) := lintegral_lintegral_swap hsw
    _ = ∫⁻ w : Fin 2 → ℝ, Gflat (w 0) (w 1) := lintegral_congr (fun w => t_integral (w 0) (w 1))
    _ = ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := lintegral_Gflat

end SingularMatrices
