import SingularMatrices.OctantIntegral

/-!
# The constant `J` (Section 4, Lemma 4.1 and Theorem 4.5)

Let `σ = (volume : Measure ℝ³).toSphere` be the surface measure on the unit sphere
(total mass `3 · vol(ball) = 4π`), and `α(u) = areaSec u` the area of the plane section
`u^⊥ ∩ [0,1]³` (2-dimensional Euclidean Hausdorff measure). Then

  `J = ∫_{S²} α(u)³ dσ(u) = 45 - 15π²/4`   (`J_eq`).

Proof:

* polar coordinates (`measurePreserving_homeomorphUnitSphereProd`) and `α(r u) = α(u)` give
  `J = ∫_{ℝ³} α(x)³ · radCut ‖x‖ dx`, since `∫₀^∞ radCut r · r² dr = 1`
  (`sphere_integral_eq`);
* off the coordinate planes, the integrand is the sum of six copies of the first-octant piece,
  moved by isometries (`Frad_ae`), so the integral is `6 · (15/2 - 5π²/8)` (`lintegral_Frad`,
  `octant_lintegral`).
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-! ### The integral over `ℝ³` -/

lemma ofReal_add6 {a b c d e f : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) :
    ENNReal.ofReal (a + b + c + d + e + f) = ENNReal.ofReal a + ENNReal.ofReal b +
      ENNReal.ofReal c + ENNReal.ofReal d + ENNReal.ofReal e + ENNReal.ofReal f := by
  rw [ENNReal.ofReal_add (by linarith) hf, ENNReal.ofReal_add (by linarith) he,
    ENNReal.ofReal_add (by linarith) hd, ENNReal.ofReal_add (by linarith) hc,
    ENNReal.ofReal_add ha hb]

theorem lintegral_Frad :
    ∫⁻ x : E3, ENNReal.ofReal (Frad x) = 6 * ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by
  let N : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.neg ℝ
  have m2 : Measurable (fun x : E3 => ENNReal.ofReal (Moct (swap12 x))) :=
    ENNReal.measurable_ofReal.comp (measurable_Moct_comp swap12.continuous.measurable)
  have m3 : Measurable (fun x : E3 => ENNReal.ofReal (Moct (swap02 x))) :=
    ENNReal.measurable_ofReal.comp (measurable_Moct_comp swap02.continuous.measurable)
  have m4 : Measurable (fun x : E3 => ENNReal.ofReal (Moct (-x))) :=
    ENNReal.measurable_ofReal.comp (measurable_Moct_comp measurable_neg)
  have m5 : Measurable (fun x : E3 => ENNReal.ofReal (Moct (-(swap12 x)))) :=
    ENNReal.measurable_ofReal.comp (measurable_Moct_comp swap12.continuous.measurable.neg)
  have m6 : Measurable (fun x : E3 => ENNReal.ofReal (Moct (-(swap02 x)))) :=
    ENNReal.measurable_ofReal.comp (measurable_Moct_comp swap02.continuous.measurable.neg)
  have hneg : ∫⁻ x : E3, ENNReal.ofReal (Moct (-x)) = ∫⁻ x : E3, ENNReal.ofReal (Moct x) :=
    N.measurePreserving.lintegral_comp_emb N.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (Moct y))
  have h12 : ∫⁻ x : E3, ENNReal.ofReal (Moct (swap12 x)) = ∫⁻ x : E3, ENNReal.ofReal (Moct x) :=
    swap12.measurePreserving.lintegral_comp_emb swap12.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (Moct y))
  have h02 : ∫⁻ x : E3, ENNReal.ofReal (Moct (swap02 x)) = ∫⁻ x : E3, ENNReal.ofReal (Moct x) :=
    swap02.measurePreserving.lintegral_comp_emb swap02.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (Moct y))
  have hn12 : ∫⁻ x : E3, ENNReal.ofReal (Moct (-(swap12 x))) =
      ∫⁻ x : E3, ENNReal.ofReal (Moct x) :=
    (swap12.measurePreserving.lintegral_comp_emb swap12.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (Moct (-y)))).trans hneg
  have hn02 : ∫⁻ x : E3, ENNReal.ofReal (Moct (-(swap02 x))) =
      ∫⁻ x : E3, ENNReal.ofReal (Moct x) :=
    (swap02.measurePreserving.lintegral_comp_emb swap02.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (Moct (-y)))).trans hneg
  have hsum : ∀ x : E3, ENNReal.ofReal (Moct x + Moct (swap12 x) + Moct (swap02 x) +
      Moct (-x) + Moct (-(swap12 x)) + Moct (-(swap02 x))) =
      ENNReal.ofReal (Moct x) + ENNReal.ofReal (Moct (swap12 x)) +
        ENNReal.ofReal (Moct (swap02 x)) + ENNReal.ofReal (Moct (-x)) +
        ENNReal.ofReal (Moct (-(swap12 x))) + ENNReal.ofReal (Moct (-(swap02 x))) :=
    fun x => ofReal_add6 (Moct_nonneg _) (Moct_nonneg _) (Moct_nonneg _) (Moct_nonneg _)
      (Moct_nonneg _) (Moct_nonneg _)
  calc
    ∫⁻ x : E3, ENNReal.ofReal (Frad x)
        = ∫⁻ x : E3,
            ENNReal.ofReal (Moct x + Moct (swap12 x) + Moct (swap02 x) + Moct (-x) +
              Moct (-(swap12 x)) + Moct (-(swap02 x))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [Frad_ae] with x hx
            rw [hx]
    _ = ∫⁻ x : E3, (ENNReal.ofReal (Moct x) + ENNReal.ofReal (Moct (swap12 x)) +
            ENNReal.ofReal (Moct (swap02 x)) + ENNReal.ofReal (Moct (-x)) +
            ENNReal.ofReal (Moct (-(swap12 x))) + ENNReal.ofReal (Moct (-(swap02 x)))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with x
          exact hsum x
    _ = 6 * ∫⁻ x : E3, ENNReal.ofReal (Moct x) := by
          -- split the integral of the sum (each summand on the right is measurable)
          rw [lintegral_add_right _ m6, lintegral_add_right _ m5, lintegral_add_right _ m4,
            lintegral_add_right _ m3, lintegral_add_right _ m2,
            h12, h02, hneg, hn12, hn02]
          ring
    _ = 6 * ENNReal.ofReal (15 / 2 - 5 * π ^ 2 / 8) := by
          rw [octant_lintegral]


theorem integral_Frad : ∫ x : E3, Frad x = 45 - 15 * π ^ 2 / 4 := by
  have hflat : 0 ≤ 15 / 2 - 5 * π ^ 2 / 8 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hmeas : Measurable (fun x : E3 => Moct x + Moct (swap12 x) + Moct (swap02 x) +
      Moct (-x) + Moct (-(swap12 x)) + Moct (-(swap02 x))) :=
    (((((measurable_Moct_comp measurable_id).add
      (measurable_Moct_comp swap12.continuous.measurable)).add
      (measurable_Moct_comp swap02.continuous.measurable)).add
      (measurable_Moct_comp measurable_neg)).add
      (measurable_Moct_comp swap12.continuous.measurable.neg)).add
      (measurable_Moct_comp swap02.continuous.measurable.neg)
  have hae : AEStronglyMeasurable Frad volume :=
    hmeas.aestronglyMeasurable.congr (Frad_ae.mono fun x hx => hx.symm)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall Frad_nonneg) hae,
    lintegral_Frad, ENNReal.toReal_mul, ENNReal.toReal_ofReal hflat,
    show (6 : ENNReal).toReal = 6 by norm_num]
  ring

/-! ### Polar coordinates -/

theorem sphere_integral_eq :
    ∫ u : Metric.sphere (0 : E3) 1, areaSec (u : E3) ^ 3 ∂(volume : Measure E3).toSphere =
      ∫ x : E3, Frad x := by
  let ψ : Ioi (0 : ℝ) → ℝ := fun r => radCut (r : ℝ)
  have hS : MeasurableSet {r : Ioi (0 : ℝ) | (r : ℝ) < 1} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hψ : ∫ r, ψ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E3 - 1)) = 1 := by
    have e : ψ = {r : Ioi (0 : ℝ) | (r : ℝ) < 1}.indicator (fun _ => (3 : ℝ)) := by
      funext r
      simp only [ψ, radCut, Set.indicator_apply, mem_ofPred_eq]
    have e2 : {r : Ioi (0 : ℝ) | (r : ℝ) < 1} = Iio ⟨1, by norm_num⟩ := by
      ext r
      exact Iff.rfl
    rw [e, integral_indicator_const _ hS, e2, measureReal_def, Measure.volumeIoiPow_apply_Iio,
      finrank_euclideanSpace_fin]
    norm_num
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E3)
  calc ∫ u : Metric.sphere (0 : E3) 1, areaSec (u : E3) ^ 3 ∂(volume : Measure E3).toSphere
      = (∫ u : Metric.sphere (0 : E3) 1, areaSec (u : E3) ^ 3 ∂(volume : Measure E3).toSphere) *
          ∫ r, ψ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E3 - 1)) := by rw [hψ, mul_one]
    _ = ∫ z : Metric.sphere (0 : E3) 1 × Ioi (0 : ℝ), areaSec (z.1 : E3) ^ 3 * ψ z.2
          ∂((volume : Measure E3).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E3 - 1))) :=
        (integral_prod_mul (fun u : Metric.sphere (0 : E3) 1 => areaSec (u : E3) ^ 3) ψ).symm
    _ = ∫ x : ({0}ᶜ : Set E3), areaSec ((homeomorphUnitSphereProd E3 x).1 : E3) ^ 3 *
          ψ (homeomorphUnitSphereProd E3 x).2 ∂(Measure.comap Subtype.val volume) :=
        (hmp.integral_comp (homeomorphUnitSphereProd E3).measurableEmbedding
          (fun z => areaSec (z.1 : E3) ^ 3 * ψ z.2)).symm
    _ = ∫ x : ({0}ᶜ : Set E3), Frad (x : E3) ∂(Measure.comap Subtype.val volume) := by
        congr 1
        funext x
        have hx : (x : E3) ≠ 0 := x.2
        show areaSec ((homeomorphUnitSphereProd E3 x).1 : E3) ^ 3 *
          radCut ((homeomorphUnitSphereProd E3 x).2 : ℝ) =
            areaSec (x : E3) ^ 3 * radCut ‖(x : E3)‖
        rw [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
          areaSec_smul (inv_ne_zero (norm_ne_zero_iff.mpr hx))]
    _ = ∫ x in ({0}ᶜ : Set E3), Frad x :=
        integral_subtype_comap (measurableSet_singleton 0).compl Frad
    _ = ∫ x : E3, Frad x := by rw [restrict_compl_singleton]

/-- **The constant `J`** (Theorem 4.5): `∫_{S²} α(u)³ dσ(u) = 45 - 15π²/4`, where `σ` is the
surface measure on the unit sphere and `α(u)` the area of `u^⊥ ∩ [0,1]³`. -/
theorem J_eq :
    ∫ u : Metric.sphere (0 : E3) 1, areaSec (u : E3) ^ 3 ∂(volume : Measure E3).toSphere =
      45 - 15 * π ^ 2 / 4 := by
  rw [sphere_integral_eq, integral_Frad]

end SingularMatrices
