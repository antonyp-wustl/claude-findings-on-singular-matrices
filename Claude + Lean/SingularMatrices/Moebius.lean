import SingularMatrices.ThreeByThree

/-!
# The Möbius formula for `g(m)` (Lemma 3.2, second identity)

`g(m)` counts primitive rows in `ℤ_{>0}³` with largest entry `m`. We prove

* `sum_gP_divisors`: `∑_{d ∣ m} g(d) + (m - 1)³ = m³`, by writing each row with largest
  entry `m` uniquely as `d • v` with `v` primitive;
* `gP_moebius`, `g3_moebius`: `g(m) = ∑_{d e = m} μ(d) (e³ - (e - 1)³)`, by Möbius inversion.
-/

namespace SingularMatrices

open Finset

lemma mem_rows3 {N : ℕ} {v : ℕ × ℕ × ℕ} :
    v ∈ rows3 N ↔ (1 ≤ v.1 ∧ v.1 ≤ N) ∧ (1 ≤ v.2.1 ∧ v.2.1 ≤ N) ∧ (1 ≤ v.2.2 ∧ v.2.2 ≤ N) := by
  simp only [rows3, entries, mem_product, mem_Icc]

lemma le_max3 (v : ℕ × ℕ × ℕ) : v.1 ≤ max3 v ∧ v.2.1 ≤ max3 v ∧ v.2.2 ≤ max3 v :=
  ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _)⟩

lemma dvd_max_aux {d a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact hb
  · rw [max_eq_left h]
    exact ha

/-- Multiply a row by `d`. -/
def smul3 (d : ℕ) (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (d * p.1, d * p.2.1, d * p.2.2)

lemma smul3_injective {d : ℕ} (hd : 0 < d) : Function.Injective (smul3 d) := by
  intro p q h
  have h1 : d * p.1 = d * q.1 := congrArg (fun t => t.1) h
  have h2 : d * p.2.1 = d * q.2.1 := congrArg (fun t => t.2.1) h
  have h3 : d * p.2.2 = d * q.2.2 := congrArg (fun t => t.2.2) h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hd h1)
    (Prod.ext (Nat.eq_of_mul_eq_mul_left hd h2) (Nat.eq_of_mul_eq_mul_left hd h3))

lemma max3_smul3 (d : ℕ) (p : ℕ × ℕ × ℕ) : max3 (smul3 d p) = d * max3 p :=
  (mul_max3 d p).symm

lemma gcd3_smul3 (d : ℕ) (p : ℕ × ℕ × ℕ) : gcd3 (smul3 d p) = d * gcd3 p := by
  show Nat.gcd (d * p.1) (Nat.gcd (d * p.2.1) (d * p.2.2)) =
    d * Nat.gcd p.1 (Nat.gcd p.2.1 p.2.2)
  rw [Nat.gcd_mul_left, Nat.gcd_mul_left]

lemma smul3_dir3 (v : ℕ × ℕ × ℕ) : smul3 (gcd3 v) (dir3 v) = v := by
  obtain ⟨h1, h2, h3⟩ := gcd3_dvd v
  exact Prod.ext (Nat.mul_div_cancel' h1)
    (Prod.ext (Nat.mul_div_cancel' h2) (Nat.mul_div_cancel' h3))

/-- Rows in `{1,…,n}³` whose largest entry is `n`. -/
def Etop (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (rows3 n).filter (fun v => max3 v = n)

/-- `g(n)`: primitive rows with largest entry `n`. -/
def gP (n : ℕ) : ℕ := ((prim3 n).filter (fun v => max3 v = n)).card

/-- `#Etop n = n³ - (n - 1)³`. -/
lemma card_Etop {n : ℕ} (hn : 1 ≤ n) : (Etop n).card + (n - 1) ^ 3 = n ^ 3 := by
  have hsub : (rows3 n).filter (fun v => v ∈ rows3 (n - 1)) = rows3 (n - 1) := by
    ext v
    rw [mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h' := mem_rows3.mp h
      exact mem_rows3.mpr ⟨⟨h'.1.1, le_trans h'.1.2 (Nat.sub_le n 1)⟩,
        ⟨h'.2.1.1, le_trans h'.2.1.2 (Nat.sub_le n 1)⟩,
        ⟨h'.2.2.1, le_trans h'.2.2.2 (Nat.sub_le n 1)⟩⟩
  have hE : Etop n = (rows3 n).filter (fun v => ¬ v ∈ rows3 (n - 1)) := by
    unfold Etop
    apply filter_congr
    intro v hv
    have hv' := mem_rows3.mp hv
    have hle : max3 v ≤ n := max_le hv'.1.2 (max_le hv'.2.1.2 hv'.2.2.2)
    have hiff : max3 v ≤ n - 1 ↔ v ∈ rows3 (n - 1) := by
      rw [mem_rows3]
      unfold max3
      rw [max_le_iff, max_le_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨hv'.1.1, h1⟩, ⟨hv'.2.1.1, h2⟩, ⟨hv'.2.2.1, h3⟩⟩
      · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩
        exact ⟨h1, h2, h3⟩
    rw [← hiff]
    omega
  have h : ((rows3 n).filter (fun v => v ∈ rows3 (n - 1))).card +
      ((rows3 n).filter (fun v => ¬ v ∈ rows3 (n - 1))).card = (rows3 n).card :=
    card_filter_add_card_filter_not _
  rw [hsub, ← hE, card_rows3, card_rows3] at h
  exact (add_comm _ _).trans h

/-- The rows in `Etop n` with gcd `d` are `d • v` with `v` primitive and `max v = n / d`. -/
lemma Etop_fiber {n d : ℕ} (hd : d ∈ n.divisors) :
    (Etop n).filter (fun v => gcd3 v = d) =
      ((prim3 (n / d)).filter (fun p => max3 p = n / d)).image (smul3 d) := by
  obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  ext v
  rw [mem_filter, mem_image]
  constructor
  · rintro ⟨hv, hg⟩
    obtain ⟨hvr, hvm⟩ := mem_filter.mp hv
    subst hg
    have hv' := mem_rows3.mp hvr
    obtain ⟨g1, g2, g3⟩ := gcd3_dvd v
    have hmax : gcd3 v * max3 (dir3 v) = n := by
      rw [← max3_smul3, smul3_dir3, hvm]
    have hq : max3 (dir3 v) = n / gcd3 v := by
      rw [← hmax, Nat.mul_div_cancel_left _ hd0]
    have hle := le_max3 (dir3 v)
    rw [hq] at hle
    refine ⟨dir3 v, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_rows3.mpr
      ⟨⟨?_, hle.1⟩, ⟨?_, hle.2.1⟩, ⟨?_, hle.2.2⟩⟩, gcd3_dir3 hv'.1.1⟩, hq⟩, smul3_dir3 v⟩
    · exact Nat.div_pos (Nat.le_of_dvd hv'.1.1 g1) hd0
    · exact Nat.div_pos (Nat.le_of_dvd hv'.2.1.1 g2) hd0
    · exact Nat.div_pos (Nat.le_of_dvd hv'.2.2.1 g3) hd0
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp', hpm⟩ := mem_filter.mp hp
    obtain ⟨hpr, hpg⟩ := mem_filter.mp hp'
    have hpv := mem_rows3.mp hpr
    have hdd : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hmx : max3 (smul3 d p) = n := by rw [max3_smul3, hpm, hdd]
    have hle := le_max3 (smul3 d p)
    rw [hmx] at hle
    refine ⟨mem_filter.mpr ⟨mem_rows3.mpr ⟨⟨Nat.mul_pos hd0 hpv.1.1, hle.1⟩,
      ⟨Nat.mul_pos hd0 hpv.2.1.1, hle.2.1⟩, ⟨Nat.mul_pos hd0 hpv.2.2.1, hle.2.2⟩⟩, hmx⟩, ?_⟩
    rw [gcd3_smul3, hpg, mul_one]

/-- `∑_{d ∣ n} g(d) + (n - 1)³ = n³`. -/
lemma sum_gP_divisors {n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, gP d + (n - 1) ^ 3 = n ^ 3 := by
  have hmaps : ∀ v ∈ Etop n, gcd3 v ∈ n.divisors := by
    intro v hv
    obtain ⟨_, hvm⟩ := mem_filter.mp hv
    obtain ⟨g1, g2, g3⟩ := gcd3_dvd v
    rw [Nat.mem_divisors]
    refine ⟨?_, hn.ne'⟩
    rw [← hvm]
    exact dvd_max_aux g1 (dvd_max_aux g2 g3)
  have hcard : (Etop n).card = ∑ d ∈ n.divisors, gP (n / d) := by
    rw [card_eq_sum_card_fiberwise (f := gcd3) (s := Etop n) (t := n.divisors)
      (fun v hv => hmaps v (mem_coe.mp hv))]
    apply sum_congr rfl
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Etop_fiber hd, card_image_of_injective _ (smul3_injective hd0), gP]
  rw [← Nat.sum_div_divisors n gP, ← hcard]
  exact card_Etop hn

/-- **Lemma 3.2**, second identity: `g(n) = ∑_{d e = n} μ(d) (e³ - (e - 1)³)`. -/
theorem gP_moebius {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * ((x.2 : ℤ) ^ 3 - ((x.2 : ℤ) - 1) ^ 3) =
        (gP n : ℤ) := by
  have key : ∀ m : ℕ, m > 0 →
      ∑ i ∈ m.divisors, (gP i : ℤ) = (m : ℤ) ^ 3 - ((m : ℤ) - 1) ^ 3 := by
    intro m hm
    have h := sum_gP_divisors hm
    have h1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    have h2 := congrArg (fun k : ℕ => (k : ℤ)) h
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_sum] at h2
    rw [h1] at h2
    linear_combination h2
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp key) n hn
  simpa only [Int.cast_id] using h

/-- `g3 N m`, counted inside the box `{1,…,N}³`, equals `g(m)` for `m ≤ N`. -/
lemma g3_eq_gP {N m : ℕ} (hmN : m ≤ N) : g3 N m = gP m := by
  unfold g3 gP
  congr 1
  ext v
  simp only [prim3, mem_filter]
  constructor
  · rintro ⟨⟨hv, hg⟩, hm⟩
    refine ⟨⟨?_, hg⟩, hm⟩
    have hle := le_max3 v
    rw [hm] at hle
    have hv' := mem_rows3.mp hv
    exact mem_rows3.mpr ⟨⟨hv'.1.1, hle.1⟩, ⟨hv'.2.1.1, hle.2.1⟩, ⟨hv'.2.2.1, hle.2.2⟩⟩
  · rintro ⟨⟨hv, hg⟩, hm⟩
    refine ⟨⟨?_, hg⟩, hm⟩
    have hv' := mem_rows3.mp hv
    exact mem_rows3.mpr ⟨⟨hv'.1.1, le_trans hv'.1.2 hmN⟩, ⟨hv'.2.1.1, le_trans hv'.2.1.2 hmN⟩,
      ⟨hv'.2.2.1, le_trans hv'.2.2.2 hmN⟩⟩

/-- **Lemma 3.2**, second identity, for the `g3 N m` of `A3count_eq_sum_g`. -/
theorem g3_moebius {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * ((x.2 : ℤ) ^ 3 - ((x.2 : ℤ) - 1) ^ 3) =
        (g3 N m : ℤ) := by
  rw [g3_eq_gP hmN]
  exact gP_moebius hm

-- Checks against the formula: g(1) = 1, g(2) = 7 - 1 = 6, g(3) = 19 - 1 = 18.
example : gP 1 = 1 := by native_decide
example : gP 2 = 6 := by native_decide
example : gP 3 = 18 := by native_decide

end SingularMatrices
