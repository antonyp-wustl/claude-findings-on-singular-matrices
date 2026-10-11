import Mathlib

/-!
# Two integrals of the logarithm (for the constant `J`, Section 4)

* `integral_pow_mul_log`: `∫₀¹ xᵏ log x dx = -1/(k+1)²`.
* `hasSum_alt_inv_sq`: `∑_{k ≥ 0} (-1)ᵏ/(k+1)² = π²/12`, from `ζ(2) = π²/6`.
* `integral_log_div_one_add`: `∫₀¹ log x/(1+x) dx = -π²/12`.

The last integral is the only source of `π²` in `J = 45 - 15π²/4`.
-/

namespace SingularMatrices

open MeasureTheory Set Real

lemma intervalIntegrable_pow_mul_log (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ k * Real.log x) volume 0 1 :=
  intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow k).continuousOn

lemma hasDerivAt_pow_succ' (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (k + 1)) (((k : ℝ) + 1) * x ^ k) x := by
  have h := hasDerivAt_pow (k + 1) x
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  exact h

/-- `∫₀¹ xᵏ log x dx = -1/(k+1)²`. -/
lemma integral_pow_mul_log (k : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ k * Real.log x = -1 / ((k : ℝ) + 1) ^ 2 := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hcont : ContinuousOn (fun x : ℝ => x ^ (k + 1) * Real.log x / ((k : ℝ) + 1) -
      x ^ (k + 1) / ((k : ℝ) + 1) ^ 2) (Icc 0 1) := by
    apply Continuous.continuousOn
    have h1 : Continuous (fun x : ℝ => x ^ k * (x * Real.log x) / ((k : ℝ) + 1)) :=
      ((continuous_pow k).mul Real.continuous_mul_log).div_const _
    have h1' : Continuous (fun x : ℝ => x ^ (k + 1) * Real.log x / ((k : ℝ) + 1)) :=
      h1.congr (fun x => by beta_reduce; ring)
    exact h1'.sub ((continuous_pow (k + 1)).div_const _)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (k + 1) * Real.log x /
      ((k : ℝ) + 1) - x ^ (k + 1) / ((k : ℝ) + 1) ^ 2) (x ^ k * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h := (((hasDerivAt_pow_succ' k x).mul (Real.hasDerivAt_log hx0)).div_const
      ((k : ℝ) + 1)).sub ((hasDerivAt_pow_succ' k x).div_const (((k : ℝ) + 1) ^ 2))
    convert h using 1
    first | ring1 | (field_simp; ring1) | field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (intervalIntegrable_pow_mul_log k)]
  have h0 : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
  simp only [one_pow, Real.log_one, h0]
  ring

/-- `∑_{k ≥ 0} (-1)ᵏ/(k+1)² = π²/12`. -/
lemma hasSum_alt_inv_sq :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  -- the even terms `1/(2k)²` sum to `π²/24`
  have he : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
    have h := hz.div_const 4
    convert h using 1
    · funext k
      push_cast
      ring
    · ring
  -- the odd terms `1/(2k+1)²` sum to `π²/8`
  have ho_s : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1)
      (fun i j (h : 2 * i + 1 = 2 * j + 1) => by omega)
  have hodd : HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
    have ht := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) he.summable ho_s
    beta_reduce at ht
    rw [he.tsum_eq, hz.tsum_eq] at ht
    have hv : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
    rw [← hv]
    exact ho_s.hasSum
  -- `1/(2(k+1))²` sums to `π²/24`, since the `k = 0` term of `he` is `0`
  have he1 : HasSum (fun k : ℕ => 1 / ((2 * (k + 1) : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
    have h := (hasSum_nat_add_iff' 1).mpr he
    convert h using 1
    simp
  have hev : HasSum (fun j : ℕ => (-1 : ℝ) ^ (2 * j) / (((2 * j : ℕ) : ℝ) + 1) ^ 2)
      (π ^ 2 / 8) := by
    convert hodd using 1
    funext j
    rw [(even_two_mul j).neg_one_pow]
    push_cast
    try ring
  have hod : HasSum (fun j : ℕ => (-1 : ℝ) ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) + 1) ^ 2)
      (-(π ^ 2 / 24)) := by
    convert he1.neg using 1
    funext j
    rw [(odd_two_mul_add_one j).neg_one_pow]
    push_cast
    try ring
  have h := HasSum.even_add_odd (f := fun k : ℕ => (-1 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2) hev hod
  convert h using 1
  ring

/-- `∫₀¹ log x/(1+x) dx = -π²/12`, by expanding `1/(1+x)` in a geometric series and
integrating term by term. -/
lemma integral_log_div_one_add :
    ∫ x in (0 : ℝ)..1, Real.log x / (1 + x) = -(π ^ 2 / 12) := by
  -- the terms
  have hint : ∀ k : ℕ, IntegrableOn (fun x : ℝ => x ^ k * Real.log x) (Ioo 0 1) :=
    fun k => (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (intervalIntegrable_pow_mul_log k)
  have hterm : ∀ k : ℕ, ∫ x in Ioo (0 : ℝ) 1, (-1 : ℝ) ^ k * (x ^ k * Real.log x) =
      (-1 : ℝ) ^ k * (-1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    rw [integral_const_mul, ← integral_pow_mul_log k, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  -- the norms of the terms have summable integrals
  have hlin : ∀ k : ℕ, ∫⁻ x in Ioo (0 : ℝ) 1, ‖(-1 : ℝ) ^ k * (x ^ k * Real.log x)‖ₑ =
      ENNReal.ofReal (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hEq : EqOn (fun x : ℝ => ‖(-1 : ℝ) ^ k * (x ^ k * Real.log x)‖ₑ)
        (fun x => ENNReal.ofReal (-(x ^ k * Real.log x))) (Ioo 0 1) := by
      intro x hx
      beta_reduce
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonpos]
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.1.le k)
        (Real.log_nonpos hx.1.le hx.2.le)
    rw [setLIntegral_congr_fun measurableSet_Ioo hEq, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_neg, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one, integral_pow_mul_log]
      ring
    · exact Integrable.neg (hint k)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.1.le k)
        (Real.log_nonpos hx.1.le hx.2.le))
  have hsum2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) :=
    hasSum_alt_inv_sq.summable.abs.congr (fun k => by
      beta_reduce
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) ^ 2 by positivity)])
  have hf' : ∑' k : ℕ, ∫⁻ x in Ioo (0 : ℝ) 1, ‖(-1 : ℝ) ^ k * (x ^ k * Real.log x)‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum2]
    exact ENNReal.ofReal_ne_top
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun x : ℝ => (-1 : ℝ) ^ k * (x ^ k * Real.log x)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun k => (measurable_const.mul ((measurable_id.pow_const k).mul
      Real.measurable_log)).aestronglyMeasurable
  have key := integral_tsum hmeas hf'
  -- the geometric series, pointwise
  have hpt : ∀ x ∈ Ioo (0 : ℝ) 1, HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (x ^ k * Real.log x))
      (Real.log x / (1 + x)) := by
    intro x hx
    have hr : |(-x)| < 1 := by
      rw [abs_neg, abs_of_pos hx.1]
      exact hx.2
    have h := (hasSum_geometric_of_abs_lt_one hr).mul_right (Real.log x)
    convert h using 1
    · funext k
      rw [neg_pow x k]
      ring
    · rw [sub_neg_eq_add, div_eq_inv_mul]
  have hL : ∫ x in Ioo (0 : ℝ) 1, Real.log x / (1 + x) =
      ∫ x in Ioo (0 : ℝ) 1, ∑' k : ℕ, (-1 : ℝ) ^ k * (x ^ k * Real.log x) :=
    setIntegral_congr_fun measurableSet_Ioo (fun x hx => (hpt x hx).tsum_eq.symm)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hL, key]
  simp_rw [hterm]
  rw [← hasSum_alt_inv_sq.neg.tsum_eq]
  congr 1
  funext k
  ring

end SingularMatrices
