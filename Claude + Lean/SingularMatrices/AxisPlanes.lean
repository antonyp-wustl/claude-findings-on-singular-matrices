import SingularMatrices.Planes

/-!
# Axis planes reduce to 2×2 (Proposition 3.5)

For the plane `a x = b y` with `gcd(a, b) = 1` and `q = ⌊N / max(a, b)⌋`:

* `axis_card`: `L_P = q N`;
* `IP_axis`: `I_P = q² N² - D(q, N)`, where `D(q, N)` (`Dgrid`) counts ordered parallel pairs in
  the grid `{1,…,q} × {1,…,N}`;
* `Dgrid_self`: `D(N, N) = S₂(N)`.

The rows on the plane are the image of the grid under the injective map `(k, z) ↦ (b k, a k, z)`.
-/

namespace SingularMatrices

open Finset

/-- The rows on the plane `a x = b y`. -/
def axisRows (N a b : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (rows3 N).filter (fun t => a * t.1 = b * t.2.1)

/-- The map `(k, z) ↦ (b k, a k, z)` from the grid onto the plane. -/
def axisMap (a b : ℕ) (x : ℕ × ℕ) : ℕ × ℕ × ℕ := (b * x.1, a * x.1, x.2)

/-- `D(q, N)`: ordered pairs `((k, z), (k', z'))` in `{1,…,q} × {1,…,N}` with `k z' = z k'`. -/
def Dgrid (q N : ℕ) : ℕ :=
  (((Icc 1 q ×ˢ Icc 1 N) ×ˢ (Icc 1 q ×ˢ Icc 1 N)).filter
    (fun x => x.1.1 * x.2.2 = x.1.2 * x.2.1)).card

/-- `D(N, N) = S₂(N)`. -/
lemma Dgrid_self (N : ℕ) : Dgrid N N = S2 N := rfl

lemma axisMap_injective {a b : ℕ} (ha : 0 < a) : Function.Injective (axisMap a b) := by
  intro x y h
  have h2 : a * x.1 = a * y.1 := congrArg (fun t => t.2.1) h
  have h3 : x.2 = y.2 := congrArg (fun t => t.2.2) h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left ha h2) h3

lemma axisPair_injective {a b : ℕ} (ha : 0 < a) :
    Function.Injective (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (axisMap a b x.1, axisMap a b x.2)) := by
  intro x y h
  have h1 : axisMap a b x.1 = axisMap a b y.1 := congrArg Prod.fst h
  have h2 : axisMap a b x.2 = axisMap a b y.2 := congrArg Prod.snd h
  exact Prod.ext (axisMap_injective ha h1) (axisMap_injective ha h2)

/-- The linear map preserves parallelism: images are parallel iff `k z' = z k'`. -/
lemma cross3_axisMap_eq_zero_iff {a b : ℕ} (ha : 0 < a) (g g' : ℕ × ℕ) :
    cross3 (axisMap a b g) (axisMap a b g') = 0 ↔ g.1 * g'.2 = g.2 * g'.1 := by
  obtain ⟨k, z⟩ := g
  obtain ⟨k', z'⟩ := g'
  simp only [cross3, axisMap, Prod.mk_eq_zero, Nat.cast_mul]
  constructor
  · rintro ⟨h1, -, -⟩
    have h : (a : ℤ) * ((k : ℤ) * z' - z * k') = 0 := by linear_combination h1
    have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have h2 := (mul_eq_zero.mp h).resolve_left ha'
    have h3 : (k : ℤ) * z' = z * k' := by linear_combination h2
    exact_mod_cast h3
  · intro h
    have h' : (k : ℤ) * z' = z * k' := by exact_mod_cast h
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (a : ℤ) * h'
    · linear_combination (-(b : ℤ)) * h'
    · ring

/-- The rows on `a x = b y` are `(b k, a k, z)` with `1 ≤ k ≤ q` and `1 ≤ z ≤ N`. -/
lemma axisRows_eq {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    axisRows N a b = (Icc 1 (N / max a b) ×ˢ Icc 1 N).image (axisMap a b) := by
  have hm : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  ext ⟨x, y, z⟩
  rw [mem_image]
  constructor
  · intro h
    simp only [axisRows, rows3, entries, mem_filter, mem_product, mem_Icc] at h
    obtain ⟨⟨⟨hx1, hxN⟩, ⟨hy1, hyN⟩, ⟨hz1, hzN⟩⟩, hxy⟩ := h
    obtain ⟨k, rfl⟩ : b ∣ x := hab.symm.dvd_of_dvd_mul_left (Dvd.intro y hxy.symm)
    have hy : y = a * k := Nat.eq_of_mul_eq_mul_left hb (by rw [← hxy]; ring)
    subst hy
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk, mul_zero] at hx1
        omega
      · exact hk
    have hkq : k ≤ N / max a b := by
      rw [Nat.le_div_iff_mul_le hm]
      rcases le_total a b with h | h
      · rw [max_eq_right h, mul_comm]
        exact hxN
      · rw [max_eq_left h, mul_comm]
        exact hyN
    exact ⟨(k, z), mem_product.mpr ⟨mem_Icc.mpr ⟨hk1, hkq⟩, mem_Icc.mpr ⟨hz1, hzN⟩⟩, rfl⟩
  · rintro ⟨⟨k, w⟩, hkw, he⟩
    have hk : k ∈ Icc 1 (N / max a b) := (mem_product.mp hkw).1
    have hw : w ∈ Icc 1 N := (mem_product.mp hkw).2
    rw [mem_Icc] at hk hw
    simp only [axisMap, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hm' : k * max a b ≤ N := (Nat.le_div_iff_mul_le hm).mp hk.2
    have h1 : b * k ≤ N := by
      calc b * k = k * b := mul_comm b k
        _ ≤ k * max a b := Nat.mul_le_mul (le_refl k) (le_max_right a b)
        _ ≤ N := hm'
    have h2 : a * k ≤ N := by
      calc a * k = k * a := mul_comm a k
        _ ≤ k * max a b := Nat.mul_le_mul (le_refl k) (le_max_left a b)
        _ ≤ N := hm'
    simp only [axisRows, rows3, entries, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨Nat.mul_pos hb hk.1, h1⟩, ⟨Nat.mul_pos ha hk.1, h2⟩, hw⟩, ?_⟩
    ring

/-- **Proposition 3.5**, first part: `L_P = q N`. -/
theorem axis_card {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    (axisRows N a b).card = N / max a b * N := by
  rw [axisRows_eq ha hb hab, card_image_of_injective _ (axisMap_injective ha)]
  simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel]

/-- The non-parallel pairs on the plane are the images of the non-parallel pairs of the grid. -/
lemma axis_pairs_eq {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    (axisRows N a b ×ˢ axisRows N a b).filter (fun x => ¬ cross3 x.1 x.2 = 0) =
      (((Icc 1 (N / max a b) ×ˢ Icc 1 N) ×ˢ (Icc 1 (N / max a b) ×ˢ Icc 1 N)).filter
        (fun x => ¬ x.1.1 * x.2.2 = x.1.2 * x.2.1)).image
        (fun x => (axisMap a b x.1, axisMap a b x.2)) := by
  rw [axisRows_eq ha hb hab]
  ext x
  rw [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨hr, hs⟩, hc⟩
    obtain ⟨g, hg, hgr⟩ := mem_image.mp hr
    obtain ⟨g', hg', hgs⟩ := mem_image.mp hs
    refine mem_image.mpr ⟨(g, g'), mem_filter.mpr ⟨mem_product.mpr ⟨hg, hg'⟩, ?_⟩, ?_⟩
    · intro hpar
      apply hc
      rw [← hgr, ← hgs]
      exact (cross3_axisMap_eq_zero_iff ha g g').mpr hpar
    · exact Prod.ext hgr hgs
  · intro h
    obtain ⟨⟨g, g'⟩, hgg, rfl⟩ := mem_image.mp h
    obtain ⟨hgg', hnp⟩ := mem_filter.mp hgg
    obtain ⟨hg, hg'⟩ := mem_product.mp hgg'
    refine ⟨⟨mem_image_of_mem (axisMap a b) hg, mem_image_of_mem (axisMap a b) hg'⟩, ?_⟩
    intro hc
    exact hnp ((cross3_axisMap_eq_zero_iff ha g g').mp hc)

/-- **Proposition 3.5**, second part: `I_P = q² N² - D(q, N)`. -/
theorem IP_axis {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    IP (axisRows N a b) = (N / max a b * N) ^ 2 - Dgrid (N / max a b) N := by
  rw [IP, axis_pairs_eq ha hb hab, card_image_of_injective _ (axisPair_injective ha)]
  have h : (((Icc 1 (N / max a b) ×ˢ Icc 1 N) ×ˢ (Icc 1 (N / max a b) ×ˢ Icc 1 N)).filter
        (fun x => x.1.1 * x.2.2 = x.1.2 * x.2.1)).card +
      (((Icc 1 (N / max a b) ×ˢ Icc 1 N) ×ˢ (Icc 1 (N / max a b) ×ˢ Icc 1 N)).filter
        (fun x => ¬ x.1.1 * x.2.2 = x.1.2 * x.2.1)).card =
      ((Icc 1 (N / max a b) ×ˢ Icc 1 N) ×ˢ (Icc 1 (N / max a b) ×ˢ Icc 1 N)).card :=
    card_filter_add_card_filter_not _
  have hG : ((Icc 1 (N / max a b) ×ˢ Icc 1 N) ×ˢ (Icc 1 (N / max a b) ×ˢ Icc 1 N)).card =
      (N / max a b * N) ^ 2 := by
    simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel]
    ring
  rw [hG] at h
  exact Nat.eq_sub_of_add_eq' h

/-- **Proposition 3.5**. -/
theorem axis_plane {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    (axisRows N a b).card = N / max a b * N ∧
      IP (axisRows N a b) = (N / max a b * N) ^ 2 - Dgrid (N / max a b) N :=
  ⟨axis_card ha hb hab, IP_axis ha hb hab⟩

end SingularMatrices
