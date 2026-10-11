import SingularMatrices.LogIntegral

/-!
# Region II of the integral `J` (Lemma 4.4)

On region II (`a, b ≤ 1 < a + b`) the integrand of Lemma 4.1 is
`α(a, b)³ = (1 - (a + b - 1)² / (2ab))³`. In the coordinates `s = a + b - 1 ∈ (0, 1]` and
`a ∈ [s, 1]` (so `b = 1 + s - a`) this is `f2 s a`, and

* `inner_integral`: `∫_s^1 f2 s a da = L(s) log s + M(s)` with explicit rational `L`, `M`;
* `regionII`: `∫₀¹ ∫_s^1 f2 s a da ds = 13/2 - 5π²/8`.

The second step splits off `(15/2) log s/(1+s)`, whose integral is `-5π²/8`
(`integral_log_div_one_add`), and integrates the rest with an explicit antiderivative.
The map `(a, b) ↦ (s, a)` is a shear with Jacobian `1`; that change of variables is done
separately.
-/

namespace SingularMatrices

open MeasureTheory Set Real

/-- The integrand of region II in the coordinates `(s, a)`, with `b = 1 + s - a`. -/
noncomputable def f2 (s a : ℝ) : ℝ := (1 - s ^ 2 / (2 * a * (1 + s - a))) ^ 3

noncomputable def κ1 (s : ℝ) : ℝ :=
  -3 * s ^ 2 * (s ^ 4 + 4 * s ^ 3 + 10 * s ^ 2 + 8 * s + 2) / (4 * (1 + s) ^ 5)
noncomputable def κ2 (s : ℝ) : ℝ := 3 * s ^ 4 * (s ^ 2 + 4 * s + 2) / (8 * (1 + s) ^ 4)
noncomputable def κ3 (s : ℝ) : ℝ := -s ^ 6 / (8 * (1 + s) ^ 3)

/-- An antiderivative of `f2 s` in `a` (partial fractions in `a` and in `1 + s - a`). -/
noncomputable def G2 (s a : ℝ) : ℝ :=
  a + κ1 s * (Real.log a - Real.log (1 + s - a)) + κ2 s * ((1 + s - a)⁻¹ - a⁻¹) +
    κ3 s / 2 * (((1 + s - a) * (1 + s - a))⁻¹ - (a * a)⁻¹)

noncomputable def Lfun (s : ℝ) : ℝ :=
  3 * s ^ 2 * (s ^ 4 + 4 * s ^ 3 + 10 * s ^ 2 + 8 * s + 2) / (2 * (1 + s) ^ 5)
noncomputable def Mfun (s : ℝ) : ℝ :=
  (s - 1) * (s ^ 6 - 4 * s ^ 5 - 31 * s ^ 4 - 44 * s ^ 3 - 48 * s ^ 2 - 32 * s - 8) /
    (8 * (1 + s) ^ 4)

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_G2 {s a : ℝ} (_hs : 0 ≤ s) (ha : 0 < a) (hd : 0 < 1 + s - a) :
    HasDerivAt (G2 s) (f2 s a) a := by
  have ha0 : a ≠ 0 := ha.ne'
  have hd0 : 1 + s - a ≠ 0 := hd.ne'
  have hc0 : 1 + s ≠ 0 := (by linarith : (0 : ℝ) < 1 + s).ne'
  have hD : HasDerivAt (fun y : ℝ => 1 + s - y) (-1) a := (hasDerivAt_id a).const_sub (1 + s)
  have h1 := (Real.hasDerivAt_log ha0).sub (hD.log hd0)
  have h2 := (hD.inv hd0).sub (hasDerivAt_inv ha0)
  have h3 := ((hD.mul hD).inv (mul_ne_zero hd0 hd0)).sub
    (((hasDerivAt_id a).mul (hasDerivAt_id a)).inv (mul_ne_zero ha0 ha0))
  have h := (((hasDerivAt_id a).add (h1.const_mul (κ1 s))).add (h2.const_mul (κ2 s))).add
    (h3.const_mul (κ3 s / 2))
  refine h.congr_deriv ?_
  simp only [f2, κ1, κ2, κ3, Pi.mul_apply, id_eq]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- `∫_s^1 f2 s a da = L(s) log s + M(s)` for `0 < s ≤ 1`. -/
lemma inner_integral {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∫ a in s..1, f2 s a = Lfun s * Real.log s + Mfun s := by
  have hs0 : s ≠ 0 := hs.ne'
  have hc0 : 1 + s ≠ 0 := (by linarith : (0 : ℝ) < 1 + s).ne'
  have hderiv : ∀ x ∈ uIcc s 1, HasDerivAt (G2 s) (f2 s x) x := by
    intro x hx
    rw [uIcc_of_le hs1] at hx
    exact hasDerivAt_G2 hs.le (by linarith [hx.1]) (by linarith [hx.2])
  have hcont : ContinuousOn (f2 s) (uIcc s 1) := by
    intro x hx
    rw [uIcc_of_le hs1] at hx
    have hx1 : 0 < x := by linarith [hx.1]
    have hx2 : 0 < 1 + s - x := by linarith [hx.2]
    have hx0 : 2 * x * (1 + s - x) ≠ 0 := (mul_pos (mul_pos two_pos hx1) hx2).ne'
    apply ContinuousAt.continuousWithinAt
    have hden : ContinuousAt (fun a : ℝ => 2 * a * (1 + s - a)) x := by fun_prop
    exact (continuousAt_const.sub (continuousAt_const.div hden hx0)).pow 3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have e1 : 1 + s - 1 = s := by ring
  have e2 : 1 + s - s = 1 := by ring
  simp only [G2, e1, e2, Real.log_one]
  simp only [κ1, κ2, κ3, Lfun, Mfun]
  field_simp
  ring

/-! ### The outer integral -/

lemma hasDerivAt_inv_one_add_pow (k : ℕ) {x : ℝ} (hx : 1 + x ≠ 0) :
    HasDerivAt (fun y : ℝ => ((1 + y) ^ (k + 1))⁻¹)
      (-((k : ℝ) + 1) * ((1 + x) ^ (k + 2))⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have h2 := (h1.pow (k + 1)).inv (pow_ne_zero (k + 1) hx)
  refine h2.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply]
  field_simp
  ring

/-- `A(s)/s` in partial fractions; `A(s) log s + B(s)` is an antiderivative of `E(s)`. -/
noncomputable def Atil (s : ℝ) : ℝ :=
  3 * s / 4 - 3 / 2 - 87 / 8 * ((1 + s) ^ 1)⁻¹ + 57 / 8 * ((1 + s) ^ 2)⁻¹ -
    21 / 8 * ((1 + s) ^ 3)⁻¹ + 3 / 8 * ((1 + s) ^ 4)⁻¹
noncomputable def Atil' (s : ℝ) : ℝ :=
  3 / 4 + 87 / 8 * ((1 + s) ^ 2)⁻¹ - 57 / 4 * ((1 + s) ^ 3)⁻¹ + 63 / 8 * ((1 + s) ^ 4)⁻¹ -
    3 / 2 * ((1 + s) ^ 5)⁻¹
noncomputable def Bfun (s : ℝ) : ℝ :=
  s ^ 4 / 32 - 3 * s ^ 3 / 8 - 3 * s ^ 2 / 16 + 37 * s / 8 - 67 / 8 * ((1 + s) ^ 1)⁻¹ +
    45 / 16 * ((1 + s) ^ 2)⁻¹ - 3 / 8 * ((1 + s) ^ 3)⁻¹
noncomputable def Bfun' (s : ℝ) : ℝ :=
  s ^ 3 / 8 - 9 * s ^ 2 / 8 - 3 * s / 8 + 37 / 8 + 67 / 8 * ((1 + s) ^ 2)⁻¹ -
    45 / 8 * ((1 + s) ^ 3)⁻¹ + 9 / 8 * ((1 + s) ^ 4)⁻¹
noncomputable def Kfun (s : ℝ) : ℝ := s * Atil s * Real.log s + Bfun s
noncomputable def Efun (s : ℝ) : ℝ := (Lfun s - 15 / (2 * (1 + s))) * Real.log s + Mfun s

lemma hasDerivAt_Atil {x : ℝ} (hx : 1 + x ≠ 0) : HasDerivAt Atil (Atil' x) x := by
  have h := (((((((hasDerivAt_id x).const_mul 3).div_const 4).sub_const (3 / 2)).sub
    ((hasDerivAt_inv_one_add_pow 0 hx).const_mul (87 / 8))).add
    ((hasDerivAt_inv_one_add_pow 1 hx).const_mul (57 / 8))).sub
    ((hasDerivAt_inv_one_add_pow 2 hx).const_mul (21 / 8))).add
    ((hasDerivAt_inv_one_add_pow 3 hx).const_mul (3 / 8))
  refine h.congr_deriv ?_
  simp only [Atil']
  try push_cast
  ring

lemma hasDerivAt_Bfun {x : ℝ} (hx : 1 + x ≠ 0) : HasDerivAt Bfun (Bfun' x) x := by
  have h := ((((((((hasDerivAt_pow_succ' 3 x).div_const 32).sub
    (((hasDerivAt_pow_succ' 2 x).const_mul 3).div_const 8)).sub
    (((hasDerivAt_pow_succ' 1 x).const_mul 3).div_const 16)).add
    (((hasDerivAt_id x).const_mul 37).div_const 8)).sub
    ((hasDerivAt_inv_one_add_pow 0 hx).const_mul (67 / 8))).add
    ((hasDerivAt_inv_one_add_pow 1 hx).const_mul (45 / 16))).sub
    ((hasDerivAt_inv_one_add_pow 2 hx).const_mul (3 / 8)))
  refine h.congr_deriv ?_
  simp only [Bfun']
  try push_cast
  ring

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_Kfun {x : ℝ} (hx : 0 < x) : HasDerivAt Kfun (Efun x) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : 1 + x ≠ 0 := (by linarith : (0 : ℝ) < 1 + x).ne'
  have h := (((hasDerivAt_id x).mul (hasDerivAt_Atil hx1)).mul (Real.hasDerivAt_log hx0)).add
    (hasDerivAt_Bfun hx1)
  refine h.congr_deriv ?_
  simp only [Efun, Lfun, Mfun, Atil, Atil', Bfun', Pi.mul_apply, id_eq]
  field_simp
  ring

lemma one_add_pos_of_mem {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) 1) : 0 < 1 + x := by
  rw [uIcc_of_le zero_le_one] at hx
  linarith [hx.1]

lemma continuousOn_L : ContinuousOn (fun s => Lfun s - 15 / (2 * (1 + s))) (uIcc 0 1) := by
  intro x hx
  have hp := one_add_pos_of_mem hx
  apply ContinuousAt.continuousWithinAt
  unfold Lfun
  have h1 : ContinuousAt (fun s : ℝ =>
      3 * s ^ 2 * (s ^ 4 + 4 * s ^ 3 + 10 * s ^ 2 + 8 * s + 2) / (2 * (1 + s) ^ 5)) x :=
    ContinuousAt.div (f := fun s : ℝ => 3 * s ^ 2 * (s ^ 4 + 4 * s ^ 3 + 10 * s ^ 2 + 8 * s + 2))
      (g := fun s : ℝ => 2 * (1 + s) ^ 5) (by fun_prop) (by fun_prop)
      (mul_ne_zero two_ne_zero (pow_ne_zero 5 hp.ne'))
  have h2 : ContinuousAt (fun s : ℝ => 15 / (2 * (1 + s))) x :=
    ContinuousAt.div (f := fun _ : ℝ => (15 : ℝ)) (g := fun s : ℝ => 2 * (1 + s))
      (by fun_prop) (by fun_prop) (mul_ne_zero two_ne_zero hp.ne')
  exact h1.sub h2

lemma continuousOn_M : ContinuousOn Mfun (uIcc 0 1) := by
  intro x hx
  have hp := one_add_pos_of_mem hx
  apply ContinuousAt.continuousWithinAt
  unfold Mfun
  exact ContinuousAt.div (f := fun s : ℝ =>
      (s - 1) * (s ^ 6 - 4 * s ^ 5 - 31 * s ^ 4 - 44 * s ^ 3 - 48 * s ^ 2 - 32 * s - 8))
    (g := fun s : ℝ => 8 * (1 + s) ^ 4) (by fun_prop) (by fun_prop)
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 hp.ne'))

lemma intervalIntegrable_Efun : IntervalIntegrable Efun volume 0 1 :=
  (intervalIntegral.intervalIntegrable_log'.continuousOn_mul continuousOn_L).add
    continuousOn_M.intervalIntegrable

/-- `∫₀¹ E(s) ds = 13/2`. -/
lemma integral_Efun : ∫ s in (0 : ℝ)..1, Efun s = 13 / 2 := by
  have hcont : ContinuousOn Kfun (Icc 0 1) := by
    intro x hx
    have hx1 : 1 + x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < 1 + x).ne'
    have e : Kfun = fun s => Atil s * (s * Real.log s) + Bfun s := by
      funext s
      unfold Kfun
      ring
    rw [e]
    exact (((hasDerivAt_Atil hx1).continuousAt.mul Real.continuous_mul_log.continuousAt).add
      (hasDerivAt_Bfun hx1).continuousAt).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun x hx => hasDerivAt_Kfun hx.1) intervalIntegrable_Efun]
  simp only [Kfun, Real.log_one, mul_zero, zero_mul, zero_add]
  norm_num [Bfun]

/-- **Lemma 4.4** (in the coordinates `s = a + b - 1`, `a`):
`∫₀¹ ∫_s^1 f2 s a da ds = 13/2 - 5π²/8`. -/
theorem regionII :
    ∫ s in (0 : ℝ)..1, ∫ a in s..1, f2 s a = 13 / 2 - 5 * π ^ 2 / 8 := by
  have hcinv : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (uIcc 0 1) := fun x hx =>
    ((continuous_const.add continuous_id).continuousAt.inv₀
      (one_add_pos_of_mem hx).ne').continuousWithinAt
  have hg : IntervalIntegrable (fun s : ℝ => Real.log s * (1 + s)⁻¹) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn hcinv
  have h1 : ∫ s in (0 : ℝ)..1, ∫ a in s..1, f2 s a =
      ∫ s in (0 : ℝ)..1, (Efun s + 15 / 2 * (Real.log s * (1 + s)⁻¹)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [uIoc_of_le zero_le_one] at hs
    rw [inner_integral hs.1 hs.2]
    have hc0 : 1 + s ≠ 0 := (by linarith [hs.1] : (0 : ℝ) < 1 + s).ne'
    unfold Efun
    field_simp
    ring
  rw [h1, intervalIntegral.integral_add intervalIntegrable_Efun (hg.const_mul (15 / 2)),
    intervalIntegral.integral_const_mul, integral_Efun]
  simp_rw [← div_eq_mul_inv]
  rw [integral_log_div_one_add]
  ring

end SingularMatrices
