import SingularMatrices.Canon
import SingularMatrices.AxisPlanes

/-!
# Lemma 3.3 and Theorem 3.6 (the exact decomposition)

Starting from `S3_normals`, `S₃(N) = N³ A(N) + ∑_w L(w) I(w)` over canonical normals `w`:

* **Lemma 3.3** (`fiber0` … `fiber5`, `rest_nonneg`): a canonical normal `w` with `L(w) ≠ 0` has
  one of six sign patterns. Three are axis planes, `a x = b y`, `a x = b z`, `a y = b z` with
  `gcd(a, b) = 1`. Three are generic planes, `a x + b y = c z`, `a x + b z = c y`,
  `a y + b z = c x` with `gcd(a, b, c) = 1`. Each plane occurs exactly once.
* Permuting coordinates (`Lw_Iw_perm`) shows that the three patterns in each class contribute
  equally.
* Axis planes are evaluated by Proposition 3.5 (`axis_plane`), and the coprime pairs are grouped
  by `m = max(a, b)`, giving `h(m) = 2φ(m)` for `m ≥ 2` and `h(1) = 1`.

The result is `exact_decomposition`, **Theorem 3.6**.
-/

namespace SingularMatrices

open Finset

/-! ### Permuting coordinates -/

lemma card_filter_perm {α : Type*} [DecidableEq α] {s : Finset α} (π π' : α → α)
    (h1 : ∀ x, π' (π x) = x) (h2 : ∀ x, π (π' x) = x) (hs : ∀ x, x ∈ s ↔ π x ∈ s)
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hpq : ∀ x, p x ↔ q (π x)) :
    (s.filter p).card = (s.filter q).card := by
  have hinj : Function.Injective π := by
    intro x y h
    calc x = π' (π x) := (h1 x).symm
      _ = π' (π y) := by rw [h]
      _ = y := h1 y
  have himg : s.filter q = (s.filter p).image π := by
    ext y
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨hy, hq⟩
      refine ⟨π' y, mem_filter.mpr ⟨(hs _).mpr ?_, (hpq _).mpr ?_⟩, h2 y⟩
      · rw [h2]
        exact hy
      · rw [h2]
        exact hq
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxs, hpx⟩ := mem_filter.mp hx
      exact ⟨(hs x).mp hxs, (hpq x).mp hpx⟩
  rw [himg, card_image_of_injective _ hinj]

/-- A coordinate permutation that preserves the box and parallelism preserves `L` and `I`. -/
lemma Lw_Iw_perm {N : ℕ} (π π' : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (h1 : ∀ t, π' (π t) = t)
    (h2 : ∀ t, π (π' t) = t) (hmem : ∀ t, t ∈ rows3 N ↔ π t ∈ rows3 N)
    (hcr : ∀ r s, cross3 (π r) (π s) = 0 ↔ cross3 r s = 0) {w w' : ℤ × ℤ × ℤ}
    (hd : ∀ t, dot3 w t = 0 ↔ dot3 w' (π t) = 0) :
    Lw N w = Lw N w' ∧ Iw N w = Iw N w' := by
  constructor
  · exact card_filter_perm π π' h1 h2 hmem hd
  · apply card_filter_perm (fun x => (π x.1, π x.2)) (fun x => (π' x.1, π' x.2))
    · intro x
      exact Prod.ext (h1 x.1) (h1 x.2)
    · intro x
      exact Prod.ext (h2 x.1) (h2 x.2)
    · intro x
      constructor
      · intro hx
        obtain ⟨hx1, hxc⟩ := mem_filter.mp hx
        obtain ⟨hr, hs⟩ := mem_product.mp hx1
        exact mem_filter.mpr ⟨mem_product.mpr ⟨(hmem _).mp hr, (hmem _).mp hs⟩,
          fun h => hxc ((hcr _ _).mp h)⟩
      · intro hx
        obtain ⟨hx1, hxc⟩ := mem_filter.mp hx
        obtain ⟨hr, hs⟩ := mem_product.mp hx1
        exact mem_filter.mpr ⟨mem_product.mpr ⟨(hmem _).mpr hr, (hmem _).mpr hs⟩,
          fun h => hxc ((hcr _ _).mpr h)⟩
    · intro x
      exact and_congr (hd _) (hd _)

/-- The cyclic permutation `(x, y, z) ↦ (y, z, x)` and its inverse. -/
def cyc (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (t.2.1, t.2.2, t.1)
def cycInv (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (t.2.2, t.1, t.2.1)
/-- The swap `(x, y, z) ↦ (x, z, y)`. -/
def swp (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (t.1, t.2.2, t.2.1)

lemma cycInv_cyc (t : ℕ × ℕ × ℕ) : cycInv (cyc t) = t := rfl
lemma cyc_cycInv (t : ℕ × ℕ × ℕ) : cyc (cycInv t) = t := rfl
lemma swp_swp (t : ℕ × ℕ × ℕ) : swp (swp t) = t := rfl

lemma cyc_mem {N : ℕ} (t : ℕ × ℕ × ℕ) : t ∈ rows3 N ↔ cyc t ∈ rows3 N := by
  rw [mem_rows3, mem_rows3]
  show _ ↔ (1 ≤ t.2.1 ∧ t.2.1 ≤ N) ∧ (1 ≤ t.2.2 ∧ t.2.2 ≤ N) ∧ (1 ≤ t.1 ∧ t.1 ≤ N)
  omega

lemma swp_mem {N : ℕ} (t : ℕ × ℕ × ℕ) : t ∈ rows3 N ↔ swp t ∈ rows3 N := by
  rw [mem_rows3, mem_rows3]
  show _ ↔ (1 ≤ t.1 ∧ t.1 ≤ N) ∧ (1 ≤ t.2.2 ∧ t.2.2 ≤ N) ∧ (1 ≤ t.2.1 ∧ t.2.1 ≤ N)
  omega

lemma cyc_cross (r s : ℕ × ℕ × ℕ) : cross3 (cyc r) (cyc s) = 0 ↔ cross3 r s = 0 := by
  simp only [cross3, cyc, Prod.mk_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

lemma swp_cross (r s : ℕ × ℕ × ℕ) : cross3 (swp r) (swp s) = 0 ↔ cross3 r s = 0 := by
  simp only [cross3, swp, Prod.mk_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-! ### The six families of planes -/

/-- Axis planes: `a x = b y`, `a x = b z`, `a y = b z`. -/
def A3v (θ : ℕ × ℕ) : ℤ × ℤ × ℤ := ((θ.1 : ℤ), -(θ.2 : ℤ), 0)
def A2v (θ : ℕ × ℕ) : ℤ × ℤ × ℤ := ((θ.1 : ℤ), 0, -(θ.2 : ℤ))
def A1v (θ : ℕ × ℕ) : ℤ × ℤ × ℤ := (0, (θ.1 : ℤ), -(θ.2 : ℤ))

/-- Generic planes: `a x + b y = c z`, `a x + b z = c y`, `a y + b z = c x`. -/
def G3v (θ : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ := ((θ.1 : ℤ), (θ.2.1 : ℤ), -(θ.2.2 : ℤ))
def G2v (θ : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ := ((θ.1 : ℤ), -(θ.2.2 : ℤ), (θ.2.1 : ℤ))
def G1v (θ : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ := ((θ.2.2 : ℤ), -(θ.1 : ℤ), -(θ.2.1 : ℤ))

lemma sym_A2 (N : ℕ) (θ : ℕ × ℕ) :
    Lw N (A2v θ) = Lw N (A3v θ) ∧ Iw N (A2v θ) = Iw N (A3v θ) := by
  apply Lw_Iw_perm swp swp swp_swp swp_swp swp_mem swp_cross
  intro t
  have e : dot3 (A2v θ) t = dot3 (A3v θ) (swp t) := by
    simp only [dot3, A2v, A3v, swp]
    ring
  rw [e]

lemma sym_A1 (N : ℕ) (θ : ℕ × ℕ) :
    Lw N (A1v θ) = Lw N (A3v θ) ∧ Iw N (A1v θ) = Iw N (A3v θ) := by
  apply Lw_Iw_perm cyc cycInv cycInv_cyc cyc_cycInv cyc_mem cyc_cross
  intro t
  have e : dot3 (A1v θ) t = dot3 (A3v θ) (cyc t) := by
    simp only [dot3, A1v, A3v, cyc]
    ring
  rw [e]

lemma sym_G2 (N : ℕ) (θ : ℕ × ℕ × ℕ) :
    Lw N (G2v θ) = Lw N (G3v θ) ∧ Iw N (G2v θ) = Iw N (G3v θ) := by
  apply Lw_Iw_perm swp swp swp_swp swp_swp swp_mem swp_cross
  intro t
  have e : dot3 (G2v θ) t = dot3 (G3v θ) (swp t) := by
    simp only [dot3, G2v, G3v, swp]
    ring
  rw [e]

lemma sym_G1 (N : ℕ) (θ : ℕ × ℕ × ℕ) :
    Lw N (G1v θ) = Lw N (G3v θ) ∧ Iw N (G1v θ) = Iw N (G3v θ) := by
  apply Lw_Iw_perm cyc cycInv cycInv_cyc cyc_cycInv cyc_mem cyc_cross
  intro t
  have e : dot3 (G1v θ) t = -dot3 (G3v θ) (cyc t) := by
    simp only [dot3, G1v, G3v, cyc]
    ring
  rw [e, neg_eq_zero]

lemma A3v_inj : Function.Injective A3v := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : ℤ) = a' := congrArg (fun w => w.1) h
  have h2 : -(b : ℤ) = -b' := congrArg (fun w => w.2.1) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  rw [ha, hb]

lemma A2v_inj : Function.Injective A2v := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : ℤ) = a' := congrArg (fun w => w.1) h
  have h2 : -(b : ℤ) = -b' := congrArg (fun w => w.2.2) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  rw [ha, hb]

lemma A1v_inj : Function.Injective A1v := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : ℤ) = a' := congrArg (fun w => w.2.1) h
  have h2 : -(b : ℤ) = -b' := congrArg (fun w => w.2.2) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  rw [ha, hb]

lemma G3v_inj : Function.Injective G3v := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h1 : (a : ℤ) = a' := congrArg (fun w => w.1) h
  have h2 : (b : ℤ) = b' := congrArg (fun w => w.2.1) h
  have h3 : -(c : ℤ) = -c' := congrArg (fun w => w.2.2) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  have hc : c = c' := by omega
  rw [ha, hb, hc]

lemma G2v_inj : Function.Injective G2v := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h1 : (a : ℤ) = a' := congrArg (fun w => w.1) h
  have h2 : -(c : ℤ) = -c' := congrArg (fun w => w.2.1) h
  have h3 : (b : ℤ) = b' := congrArg (fun w => w.2.2) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  have hc : c = c' := by omega
  rw [ha, hb, hc]

lemma G1v_inj : Function.Injective G1v := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h1 : (c : ℤ) = c' := congrArg (fun w => w.1) h
  have h2 : -(a : ℤ) = -a' := congrArg (fun w => w.2.1) h
  have h3 : -(b : ℤ) = -b' := congrArg (fun w => w.2.2) h
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  have hc : c = c' := by omega
  rw [ha, hb, hc]

/-! ### Lemma 3.3: classification by sign pattern -/

/-- The sign pattern of a canonical normal: `0`–`2` axis planes, `3`–`5` generic planes,
`6` no rows at all. -/
def cls (w : ℤ × ℤ × ℤ) : ℕ :=
  if 0 < w.1 ∧ w.2.1 < 0 ∧ w.2.2 = 0 then 0
  else if 0 < w.1 ∧ w.2.1 = 0 ∧ w.2.2 < 0 then 1
  else if w.1 = 0 ∧ 0 < w.2.1 ∧ w.2.2 < 0 then 2
  else if 0 < w.1 ∧ 0 < w.2.1 ∧ w.2.2 < 0 then 3
  else if 0 < w.1 ∧ w.2.1 < 0 ∧ 0 < w.2.2 then 4
  else if 0 < w.1 ∧ w.2.1 < 0 ∧ w.2.2 < 0 then 5
  else 6

lemma cls_lt (w : ℤ × ℤ × ℤ) : cls w < 7 := by
  unfold cls
  split_ifs <;> omega

lemma gcd_rot (a b c : ℕ) : Nat.gcd a (Nat.gcd b c) = Nat.gcd b (Nat.gcd c a) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
      (Nat.dvd_gcd ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
        (Nat.gcd_dvd_left _ _))
  · exact Nat.dvd_gcd ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))

/-- Pattern `(+, -, 0)`: the planes `a x = b y`. -/
lemma fiber0 (B : ℕ) : (Wbox B).filter (fun w => cls w = 0) = (prim B).image A3v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 0 ↔ (0 < w.1 ∧ w.2.1 < 0 ∧ w.2.2 = 0) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      exact h0
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨hb1, hb2, -⟩, hg, -⟩ := mem_Wbox.mp hw
    have e1 : ((w.1.natAbs : ℕ) : ℤ) = w.1 := Int.natAbs_of_nonneg h1.le
    have e2 : ((w.2.1.natAbs : ℕ) : ℤ) = -w.2.1 := Int.ofNat_natAbs_of_nonpos h2.le
    have hcop : Nat.Coprime w.1.natAbs w.2.1.natAbs := by
      have g := hg
      unfold gZ at g
      rw [h3, Int.natAbs_zero, Nat.gcd_zero_right] at g
      exact g
    refine ⟨(w.1.natAbs, w.2.1.natAbs), ?_, ?_⟩
    · simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hcop⟩ <;> omega
    · apply Prod.ext
      · show ((w.1.natAbs : ℕ) : ℤ) = w.1
        exact e1
      · apply Prod.ext
        · show -((w.2.1.natAbs : ℕ) : ℤ) = w.2.1
          rw [e2, neg_neg]
        · show (0 : ℤ) = w.2.2
          exact h3.symm
  · rintro ⟨⟨a, b⟩, hθ, rfl⟩
    simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, hb1, hbB⟩, hcop⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ a ∧ (a : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ -(b : ℤ) ∧ -(b : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ B)
      omega
    · show Nat.gcd ((a : ℤ)).natAbs (Nat.gcd (-(b : ℤ)).natAbs (0 : ℤ).natAbs) = 1
      rw [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero, Nat.gcd_zero_right]
      exact hcop
    · exact Or.inl (show (0 : ℤ) < a by omega)
    · show (0 : ℤ) < a ∧ -(b : ℤ) < 0 ∧ (0 : ℤ) = 0
      omega

/-- Pattern `(+, 0, -)`: the planes `a x = b z`. -/
lemma fiber1 (B : ℕ) : (Wbox B).filter (fun w => cls w = 1) = (prim B).image A2v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 1 ↔ (0 < w.1 ∧ w.2.1 = 0 ∧ w.2.2 < 0) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      all_goals first | exact h1 | exact absurd h (by decide)
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨hb1, -, hb3⟩, hg, -⟩ := mem_Wbox.mp hw
    have e1 : ((w.1.natAbs : ℕ) : ℤ) = w.1 := Int.natAbs_of_nonneg h1.le
    have e3 : ((w.2.2.natAbs : ℕ) : ℤ) = -w.2.2 := Int.ofNat_natAbs_of_nonpos h3.le
    have hcop : Nat.Coprime w.1.natAbs w.2.2.natAbs := by
      have g := hg
      unfold gZ at g
      rw [h2, Int.natAbs_zero, Nat.gcd_zero_left] at g
      exact g
    refine ⟨(w.1.natAbs, w.2.2.natAbs), ?_, ?_⟩
    · simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hcop⟩ <;> omega
    · apply Prod.ext
      · show ((w.1.natAbs : ℕ) : ℤ) = w.1
        exact e1
      · apply Prod.ext
        · show (0 : ℤ) = w.2.1
          exact h2.symm
        · show -((w.2.2.natAbs : ℕ) : ℤ) = w.2.2
          rw [e3, neg_neg]
  · rintro ⟨⟨a, b⟩, hθ, rfl⟩
    simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, hb1, hbB⟩, hcop⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ a ∧ (a : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ -(b : ℤ) ∧ -(b : ℤ) ≤ B)
      omega
    · show Nat.gcd ((a : ℤ)).natAbs (Nat.gcd (0 : ℤ).natAbs (-(b : ℤ)).natAbs) = 1
      rw [Int.natAbs_natCast, Int.natAbs_zero, Int.natAbs_neg, Int.natAbs_natCast, Nat.gcd_zero_left]
      exact hcop
    · exact Or.inl (show (0 : ℤ) < a by omega)
    · show (0 : ℤ) < a ∧ (0 : ℤ) = 0 ∧ -(b : ℤ) < 0
      omega

/-- Pattern `(0, +, -)`: the planes `a y = b z`. -/
lemma fiber2 (B : ℕ) : (Wbox B).filter (fun w => cls w = 2) = (prim B).image A1v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 2 ↔ (w.1 = 0 ∧ 0 < w.2.1 ∧ w.2.2 < 0) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      all_goals first | exact h2 | exact absurd h (by decide)
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨-, hb2, hb3⟩, hg, -⟩ := mem_Wbox.mp hw
    have e2 : ((w.2.1.natAbs : ℕ) : ℤ) = w.2.1 := Int.natAbs_of_nonneg h2.le
    have e3 : ((w.2.2.natAbs : ℕ) : ℤ) = -w.2.2 := Int.ofNat_natAbs_of_nonpos h3.le
    have hcop : Nat.Coprime w.2.1.natAbs w.2.2.natAbs := by
      have g := hg
      unfold gZ at g
      rw [h1, Int.natAbs_zero, Nat.gcd_zero_left] at g
      exact g
    refine ⟨(w.2.1.natAbs, w.2.2.natAbs), ?_, ?_⟩
    · simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hcop⟩ <;> omega
    · apply Prod.ext
      · show (0 : ℤ) = w.1
        exact h1.symm
      · apply Prod.ext
        · show ((w.2.1.natAbs : ℕ) : ℤ) = w.2.1
          exact e2
        · show -((w.2.2.natAbs : ℕ) : ℤ) = w.2.2
          rw [e3, neg_neg]
  · rintro ⟨⟨a, b⟩, hθ, rfl⟩
    simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, hb1, hbB⟩, hcop⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ a ∧ (a : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ -(b : ℤ) ∧ -(b : ℤ) ≤ B)
      omega
    · show Nat.gcd (0 : ℤ).natAbs (Nat.gcd ((a : ℤ)).natAbs (-(b : ℤ)).natAbs) = 1
      rw [Int.natAbs_zero, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast, Nat.gcd_zero_left]
      exact hcop
    · exact Or.inr (Or.inl ⟨rfl, show (0 : ℤ) < a by omega⟩)
    · show (0 : ℤ) = 0 ∧ (0 : ℤ) < a ∧ -(b : ℤ) < 0
      omega

/-- Pattern `(+, +, -)`: the planes `a x + b y = c z`. -/
lemma fiber3 (B : ℕ) : (Wbox B).filter (fun w => cls w = 3) = (prim3 B).image G3v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 3 ↔ (0 < w.1 ∧ 0 < w.2.1 ∧ w.2.2 < 0) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      all_goals first | exact h3 | exact absurd h (by decide)
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨hb1, hb2, hb3⟩, hg, -⟩ := mem_Wbox.mp hw
    have e1 : ((w.1.natAbs : ℕ) : ℤ) = w.1 := Int.natAbs_of_nonneg h1.le
    have e2 : ((w.2.1.natAbs : ℕ) : ℤ) = w.2.1 := Int.natAbs_of_nonneg h2.le
    have e3 : ((w.2.2.natAbs : ℕ) : ℤ) = -w.2.2 := Int.ofNat_natAbs_of_nonpos h3.le
    have hθ : (w.1.natAbs, w.2.1.natAbs, w.2.2.natAbs) ∈ prim3 B := by
      refine mem_filter.mpr ⟨mem_rows3.mpr ?_, hg⟩
      show (1 ≤ w.1.natAbs ∧ w.1.natAbs ≤ B) ∧ (1 ≤ w.2.1.natAbs ∧ w.2.1.natAbs ≤ B) ∧
        (1 ≤ w.2.2.natAbs ∧ w.2.2.natAbs ≤ B)
      omega
    refine ⟨(w.1.natAbs, w.2.1.natAbs, w.2.2.natAbs), hθ, ?_⟩
    apply Prod.ext
    · show ((w.1.natAbs : ℕ) : ℤ) = w.1
      exact e1
    · apply Prod.ext
      · show ((w.2.1.natAbs : ℕ) : ℤ) = w.2.1
        exact e2
      · show -((w.2.2.natAbs : ℕ) : ℤ) = w.2.2
        rw [e3, neg_neg]
  · rintro ⟨⟨a, b, c⟩, hθ, rfl⟩
    simp only [prim3, mem_filter, mem_rows3] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, ⟨hb1, hbB⟩, ⟨hc1, hcB⟩⟩, hg⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ a ∧ (a : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ b ∧ (b : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ -(c : ℤ) ∧ -(c : ℤ) ≤ B)
      omega
    · show Nat.gcd ((a : ℤ)).natAbs (Nat.gcd ((b : ℤ)).natAbs (-(c : ℤ)).natAbs) = 1
      rw [Int.natAbs_natCast, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      exact hg
    · exact Or.inl (show (0 : ℤ) < a by omega)
    · show (0 : ℤ) < a ∧ (0 : ℤ) < b ∧ -(c : ℤ) < 0
      omega

/-- Pattern `(+, -, +)`: the planes `a x + b z = c y`. -/
lemma fiber4 (B : ℕ) : (Wbox B).filter (fun w => cls w = 4) = (prim3 B).image G2v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 4 ↔ (0 < w.1 ∧ w.2.1 < 0 ∧ 0 < w.2.2) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      all_goals first | exact h4 | exact absurd h (by decide)
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨hb1, hb2, hb3⟩, hg, -⟩ := mem_Wbox.mp hw
    have e1 : ((w.1.natAbs : ℕ) : ℤ) = w.1 := Int.natAbs_of_nonneg h1.le
    have e2 : ((w.2.1.natAbs : ℕ) : ℤ) = -w.2.1 := Int.ofNat_natAbs_of_nonpos h2.le
    have e3 : ((w.2.2.natAbs : ℕ) : ℤ) = w.2.2 := Int.natAbs_of_nonneg h3.le
    have hθ : (w.1.natAbs, w.2.2.natAbs, w.2.1.natAbs) ∈ prim3 B := by
      refine mem_filter.mpr ⟨mem_rows3.mpr ?_, ?_⟩
      · show (1 ≤ w.1.natAbs ∧ w.1.natAbs ≤ B) ∧ (1 ≤ w.2.2.natAbs ∧ w.2.2.natAbs ≤ B) ∧
          (1 ≤ w.2.1.natAbs ∧ w.2.1.natAbs ≤ B)
        omega
      · show Nat.gcd w.1.natAbs (Nat.gcd w.2.2.natAbs w.2.1.natAbs) = 1
        rw [Nat.gcd_comm w.2.2.natAbs w.2.1.natAbs]
        exact hg
    refine ⟨(w.1.natAbs, w.2.2.natAbs, w.2.1.natAbs), hθ, ?_⟩
    apply Prod.ext
    · show ((w.1.natAbs : ℕ) : ℤ) = w.1
      exact e1
    · apply Prod.ext
      · show -((w.2.1.natAbs : ℕ) : ℤ) = w.2.1
        rw [e2, neg_neg]
      · show ((w.2.2.natAbs : ℕ) : ℤ) = w.2.2
        exact e3
  · rintro ⟨⟨a, b, c⟩, hθ, rfl⟩
    simp only [prim3, mem_filter, mem_rows3] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, ⟨hb1, hbB⟩, ⟨hc1, hcB⟩⟩, hg⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ a ∧ (a : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ -(c : ℤ) ∧ -(c : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ b ∧ (b : ℤ) ≤ B)
      omega
    · show Nat.gcd ((a : ℤ)).natAbs (Nat.gcd (-(c : ℤ)).natAbs ((b : ℤ)).natAbs) = 1
      rw [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_natCast, Nat.gcd_comm c b]
      exact hg
    · exact Or.inl (show (0 : ℤ) < a by omega)
    · show (0 : ℤ) < a ∧ -(c : ℤ) < 0 ∧ (0 : ℤ) < b
      omega

/-- Pattern `(+, -, -)`: the planes `a y + b z = c x`. -/
lemma fiber5 (B : ℕ) : (Wbox B).filter (fun w => cls w = 5) = (prim3 B).image G1v := by
  ext w
  rw [mem_filter, mem_image]
  have hcls : cls w = 5 ↔ (0 < w.1 ∧ w.2.1 < 0 ∧ w.2.2 < 0) := by
    constructor
    · intro h
      unfold cls at h
      split_ifs at h with h0 h1 h2 h3 h4 h5
      all_goals first | exact h5 | exact absurd h (by decide)
    · rintro ⟨p1, p2, p3⟩
      unfold cls
      split_ifs with h0 h1 h2 h3 h4 h5 <;>
        first | rfl | (exfalso; omega)
  rw [hcls]
  constructor
  · rintro ⟨hw, h1, h2, h3⟩
    obtain ⟨⟨hb1, hb2, hb3⟩, hg, -⟩ := mem_Wbox.mp hw
    have e1 : ((w.1.natAbs : ℕ) : ℤ) = w.1 := Int.natAbs_of_nonneg h1.le
    have e2 : ((w.2.1.natAbs : ℕ) : ℤ) = -w.2.1 := Int.ofNat_natAbs_of_nonpos h2.le
    have e3 : ((w.2.2.natAbs : ℕ) : ℤ) = -w.2.2 := Int.ofNat_natAbs_of_nonpos h3.le
    have hθ : (w.2.1.natAbs, w.2.2.natAbs, w.1.natAbs) ∈ prim3 B := by
      refine mem_filter.mpr ⟨mem_rows3.mpr ?_, ?_⟩
      · show (1 ≤ w.2.1.natAbs ∧ w.2.1.natAbs ≤ B) ∧ (1 ≤ w.2.2.natAbs ∧ w.2.2.natAbs ≤ B) ∧
          (1 ≤ w.1.natAbs ∧ w.1.natAbs ≤ B)
        omega
      · show Nat.gcd w.2.1.natAbs (Nat.gcd w.2.2.natAbs w.1.natAbs) = 1
        rw [← gcd_rot]
        exact hg
    refine ⟨(w.2.1.natAbs, w.2.2.natAbs, w.1.natAbs), hθ, ?_⟩
    apply Prod.ext
    · show ((w.1.natAbs : ℕ) : ℤ) = w.1
      exact e1
    · apply Prod.ext
      · show -((w.2.1.natAbs : ℕ) : ℤ) = w.2.1
        rw [e2, neg_neg]
      · show -((w.2.2.natAbs : ℕ) : ℤ) = w.2.2
        rw [e3, neg_neg]
  · rintro ⟨⟨a, b, c⟩, hθ, rfl⟩
    simp only [prim3, mem_filter, mem_rows3] at hθ
    obtain ⟨⟨⟨ha1, haB⟩, ⟨hb1, hbB⟩, ⟨hc1, hcB⟩⟩, hg⟩ := hθ
    refine ⟨mem_Wbox.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · show (-(B : ℤ) ≤ c ∧ (c : ℤ) ≤ B) ∧ (-(B : ℤ) ≤ -(a : ℤ) ∧ -(a : ℤ) ≤ B) ∧
        (-(B : ℤ) ≤ -(b : ℤ) ∧ -(b : ℤ) ≤ B)
      omega
    · show Nat.gcd ((c : ℤ)).natAbs (Nat.gcd (-(a : ℤ)).natAbs (-(b : ℤ)).natAbs) = 1
      rw [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast,
        ← gcd_rot b c a, ← gcd_rot a b c]
      exact hg
    · exact Or.inl (show (0 : ℤ) < c by omega)
    · show (0 : ℤ) < c ∧ -(a : ℤ) < 0 ∧ -(b : ℤ) < 0
      omega

/-- The remaining canonical normals have no negative entry, so no row is orthogonal to them. -/
lemma rest_nonneg {w : ℤ × ℤ × ℤ} (hc : isCanon w) (h6 : cls w = 6) :
    0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2 ∧ 0 < w.1 + w.2.1 + w.2.2 := by
  unfold cls at h6
  split_ifs at h6 with h0 h1 h2 h3 h4 h5
  all_goals try exact absurd h6 (by decide)
  unfold isCanon at hc
  rcases lt_trichotomy w.2.1 0 with hb | hb | hb <;>
    rcases lt_trichotomy w.2.2 0 with hc' | hc' | hc' <;>
    rcases hc with ha | ⟨ha, ha'⟩ | ⟨ha, ha', ha''⟩ <;>
    first
    | exact (h0 ⟨by assumption, by assumption, by assumption⟩).elim
    | exact (h1 ⟨by assumption, by assumption, by assumption⟩).elim
    | exact (h2 ⟨by assumption, by assumption, by assumption⟩).elim
    | exact (h3 ⟨by assumption, by assumption, by assumption⟩).elim
    | exact (h4 ⟨by assumption, by assumption, by assumption⟩).elim
    | exact (h5 ⟨by assumption, by assumption, by assumption⟩).elim
    | (exfalso; omega)
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)

lemma Lw_eq_zero_of_nonneg {N : ℕ} {w : ℤ × ℤ × ℤ} (h1 : 0 ≤ w.1) (h2 : 0 ≤ w.2.1)
    (h3 : 0 ≤ w.2.2) (hpos : 0 < w.1 + w.2.1 + w.2.2) : Lw N w = 0 := by
  unfold Lw
  rw [card_eq_zero, filter_eq_empty_iff]
  intro t ht
  have ht' := mem_rows3.mp ht
  have k1 : (1 : ℤ) ≤ t.1 := by exact_mod_cast ht'.1.1
  have k2 : (1 : ℤ) ≤ t.2.1 := by exact_mod_cast ht'.2.1.1
  have k3 : (1 : ℤ) ≤ t.2.2 := by exact_mod_cast ht'.2.2.1
  have m1 := mul_le_mul_of_nonneg_left k1 h1
  have m2 := mul_le_mul_of_nonneg_left k2 h2
  have m3 := mul_le_mul_of_nonneg_left k3 h3
  unfold dot3
  intro h
  linarith

/-- Lemma 3.3 and the symmetry: the sum over canonical normals is three times the axis-plane
sum plus three times the generic-plane sum. -/
theorem sum_Wbox_split (N : ℕ) :
    ∑ w ∈ Wbox (N ^ 2), Lw N w * Iw N w =
      3 * ∑ θ ∈ prim (N ^ 2), Lw N (A3v θ) * Iw N (A3v θ) +
      3 * ∑ θ ∈ prim3 (N ^ 2), Lw N (G3v θ) * Iw N (G3v θ) := by
  have hmaps : ∀ w ∈ Wbox (N ^ 2), cls w ∈ range 7 := fun w _ => mem_range.mpr (cls_lt w)
  have e0 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 0), Lw N w * Iw N w =
      ∑ θ ∈ prim (N ^ 2), Lw N (A3v θ) * Iw N (A3v θ) := by
    rw [fiber0, sum_image (g := A3v) (fun x _ y _ h => A3v_inj h)]
  have e1 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 1), Lw N w * Iw N w =
      ∑ θ ∈ prim (N ^ 2), Lw N (A3v θ) * Iw N (A3v θ) := by
    rw [fiber1, sum_image (g := A2v) (fun x _ y _ h => A2v_inj h)]
    apply sum_congr rfl
    intro θ _
    obtain ⟨hL, hI⟩ := sym_A2 N θ
    rw [hL, hI]
  have e2 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 2), Lw N w * Iw N w =
      ∑ θ ∈ prim (N ^ 2), Lw N (A3v θ) * Iw N (A3v θ) := by
    rw [fiber2, sum_image (g := A1v) (fun x _ y _ h => A1v_inj h)]
    apply sum_congr rfl
    intro θ _
    obtain ⟨hL, hI⟩ := sym_A1 N θ
    rw [hL, hI]
  have e3 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 3), Lw N w * Iw N w =
      ∑ θ ∈ prim3 (N ^ 2), Lw N (G3v θ) * Iw N (G3v θ) := by
    rw [fiber3, sum_image (g := G3v) (fun x _ y _ h => G3v_inj h)]
  have e4 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 4), Lw N w * Iw N w =
      ∑ θ ∈ prim3 (N ^ 2), Lw N (G3v θ) * Iw N (G3v θ) := by
    rw [fiber4, sum_image (g := G2v) (fun x _ y _ h => G2v_inj h)]
    apply sum_congr rfl
    intro θ _
    obtain ⟨hL, hI⟩ := sym_G2 N θ
    rw [hL, hI]
  have e5 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 5), Lw N w * Iw N w =
      ∑ θ ∈ prim3 (N ^ 2), Lw N (G3v θ) * Iw N (G3v θ) := by
    rw [fiber5, sum_image (g := G1v) (fun x _ y _ h => G1v_inj h)]
    apply sum_congr rfl
    intro θ _
    obtain ⟨hL, hI⟩ := sym_G1 N θ
    rw [hL, hI]
  have e6 : ∑ w ∈ (Wbox (N ^ 2)).filter (fun w => cls w = 6), Lw N w * Iw N w = 0 := by
    apply sum_eq_zero
    intro w hw
    obtain ⟨hwB, hc6⟩ := mem_filter.mp hw
    obtain ⟨-, -, hcan⟩ := mem_Wbox.mp hwB
    obtain ⟨n1, n2, n3, hpos⟩ := rest_nonneg hcan hc6
    rw [Lw_eq_zero_of_nonneg n1 n2 n3 hpos, zero_mul]
  rw [← sum_fiberwise_of_maps_to hmaps]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [e0, e1, e2, e3, e4, e5, e6]
  ring

/-! ### Evaluating the axis and generic families -/

lemma rowsOn_A3v (N a b : ℕ) :
    (rows3 N).filter (fun t => dot3 (A3v (a, b)) t = 0) = axisRows N a b := by
  unfold axisRows
  apply filter_congr
  intro t _
  have e : dot3 (A3v (a, b)) t = ((a * t.1 : ℕ) : ℤ) - ((b * t.2.1 : ℕ) : ℤ) := by
    simp only [dot3, A3v]
    push_cast
    ring
  rw [e, sub_eq_zero]
  exact Nat.cast_inj

lemma Lw_A3v_eq (N a b : ℕ) : Lw N (A3v (a, b)) = (axisRows N a b).card := by
  unfold Lw
  rw [rowsOn_A3v]

lemma Iw_A3v_eq (N a b : ℕ) : Iw N (A3v (a, b)) = IP (axisRows N a b) := by
  rw [Iw_eq_IP, rowsOn_A3v]

/-- The rows on the generic plane `a x + b y = c z`. -/
def genRows (N : ℕ) (θ : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (rows3 N).filter (fun t => θ.1 * t.1 + θ.2.1 * t.2.1 = θ.2.2 * t.2.2)

lemma rowsOn_G3v (N : ℕ) (θ : ℕ × ℕ × ℕ) :
    (rows3 N).filter (fun t => dot3 (G3v θ) t = 0) = genRows N θ := by
  unfold genRows
  apply filter_congr
  intro t _
  have e : dot3 (G3v θ) t =
      ((θ.1 * t.1 + θ.2.1 * t.2.1 : ℕ) : ℤ) - ((θ.2.2 * t.2.2 : ℕ) : ℤ) := by
    simp only [dot3, G3v]
    push_cast
    ring
  rw [e, sub_eq_zero]
  exact Nat.cast_inj

lemma Lw_G3v_eq (N : ℕ) (θ : ℕ × ℕ × ℕ) : Lw N (G3v θ) = (genRows N θ).card := by
  unfold Lw
  rw [rowsOn_G3v]

/-- Axis planes with `max(a, b) > N` contain no rows. -/
lemma axis_sum_reduce (N : ℕ) :
    ∑ θ ∈ prim (N ^ 2), Lw N (A3v θ) * Iw N (A3v θ) =
      ∑ θ ∈ prim N, Lw N (A3v θ) * Iw N (A3v θ) := by
  have hN : N ≤ N ^ 2 := by
    rw [sq]
    exact Nat.le_mul_self N
  symm
  apply sum_subset
  · intro θ hθ
    simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hc⟩ := hθ
    exact ⟨⟨⟨h1, le_trans h2 hN⟩, h3, le_trans h4 hN⟩, hc⟩
  · rintro ⟨a, b⟩ hθ hnot
    simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ hnot
    obtain ⟨⟨⟨ha1, _⟩, hb1, _⟩, hc⟩ := hθ
    have hmax : N < max a b := by
      by_contra hle
      have hle' : max a b ≤ N := not_lt.mp hle
      exact hnot ⟨⟨⟨ha1, le_trans (le_max_left a b) hle'⟩, hb1,
        le_trans (le_max_right a b) hle'⟩, hc⟩
    rw [Lw_A3v_eq, axis_card ha1 hb1 hc, Nat.div_eq_of_lt hmax, zero_mul, zero_mul]

/-! ### Grouping coprime pairs by their maximum -/

lemma sum_primBelow_F (N : ℕ) (F : ℕ → ℕ) :
    ∑ v ∈ primBelow N, F (max v.1 v.2) = ∑ m ∈ Icc 1 N, Nat.totient m * F m := by
  rw [sum_finset_product (primBelow N) (Icc 1 N) (fun p => (Icc 1 p).filter (Nat.Coprime p))]
  · apply sum_congr rfl
    intro p _
    have hval : ∀ q ∈ (Icc 1 p).filter (Nat.Coprime p), F (max (p, q).1 (p, q).2) = F p := by
      intro q hq
      have hqp : q ≤ p := (mem_Icc.mp (mem_filter.mp hq).1).2
      show F (max p q) = F p
      rw [max_eq_left hqp]
    rw [sum_congr rfl hval, sum_const, smul_eq_mul, card_coprime_Icc]
  · rintro ⟨p, q⟩
    simp only [primBelow, prim, rows2, entries, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hp1, hpN⟩, hq1, _⟩, hc⟩, hqp⟩
      exact ⟨⟨hp1, hpN⟩, ⟨hq1, hqp⟩, hc⟩
    · rintro ⟨⟨hp1, hpN⟩, ⟨hq1, hqp⟩, hc⟩
      exact ⟨⟨⟨⟨hp1, hpN⟩, hq1, le_trans hqp hpN⟩, hc⟩, hqp⟩

lemma sum_primAbove_F (N : ℕ) (F : ℕ → ℕ) :
    ∑ v ∈ primAbove N, F (max v.1 v.2) = ∑ m ∈ Icc 1 N, Nat.totient m * F m := by
  rw [sum_finset_product_right (primAbove N) (Icc 1 N)
    (fun q => (Icc 1 q).filter (Nat.Coprime q))]
  · apply sum_congr rfl
    intro q _
    have hval : ∀ p ∈ (Icc 1 q).filter (Nat.Coprime q), F (max (p, q).1 (p, q).2) = F q := by
      intro p hp
      have hpq : p ≤ q := (mem_Icc.mp (mem_filter.mp hp).1).2
      show F (max p q) = F q
      rw [max_eq_right hpq]
    rw [sum_congr rfl hval, sum_const, smul_eq_mul, card_coprime_Icc]
  · rintro ⟨p, q⟩
    simp only [primAbove, prim, rows2, entries, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hp1, _⟩, hq1, hqN⟩, hc⟩, hpq⟩
      exact ⟨⟨hq1, hqN⟩, ⟨hp1, hpq⟩, hc.symm⟩
    · rintro ⟨⟨hq1, hqN⟩, ⟨hp1, hpq⟩, hc⟩
      exact ⟨⟨⟨⟨hp1, le_trans hpq hqN⟩, hq1, hqN⟩, hc.symm⟩, hpq⟩

lemma sum_primInter_F (N : ℕ) (F : ℕ → ℕ) (hN : 1 ≤ N) :
    ∑ v ∈ primBelow N ∩ primAbove N, F (max v.1 v.2) = F 1 := by
  have hset : primBelow N ∩ primAbove N = {(1, 1)} := by
    ext ⟨p, q⟩
    simp only [primBelow, primAbove, prim, rows2, entries, mem_inter, mem_filter, mem_product,
      mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨_, hc⟩, hqp⟩, _, hpq⟩
      have hpq' : p = q := le_antisymm hpq hqp
      rw [← hpq'] at hc
      have hp : p = 1 := (Nat.coprime_self p).mp hc
      exact ⟨hp, hpq'.symm.trans hp⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨⟨⟨le_refl 1, hN⟩, le_refl 1, hN⟩, Nat.coprime_one_left 1⟩, le_refl 1⟩,
        ⟨⟨⟨le_refl 1, hN⟩, le_refl 1, hN⟩, Nat.coprime_one_left 1⟩, le_refl 1⟩
  rw [hset, sum_singleton]
  show F (max 1 1) = F 1
  rw [max_self]

lemma sum_prim_max (N : ℕ) (F : ℕ → ℕ) (hN : 1 ≤ N) :
    ∑ v ∈ prim N, F (max v.1 v.2) + F 1 = 2 * ∑ m ∈ Icc 1 N, Nat.totient m * F m := by
  have h : ∑ v ∈ primBelow N ∪ primAbove N, F (max v.1 v.2) +
      ∑ v ∈ primBelow N ∩ primAbove N, F (max v.1 v.2) =
      ∑ v ∈ primBelow N, F (max v.1 v.2) + ∑ v ∈ primAbove N, F (max v.1 v.2) :=
    sum_union_inter
  rw [primBelow_union_primAbove, sum_primInter_F N F hN, sum_primBelow_F N F,
    sum_primAbove_F N F] at h
  rw [h]
  ring

/-- `h(m)`: the number of coprime ordered pairs `(a, b)` with `max(a, b) = m`. -/
def hfun (m : ℕ) : ℕ := if m = 1 then 1 else 2 * Nat.totient m

/-- `∑_{(a,b) coprime in [1,N]²} F(max(a, b)) = ∑_{m ≤ N} h(m) F(m)`. -/
lemma sum_prim_max_h (N : ℕ) (F : ℕ → ℕ) :
    ∑ v ∈ prim N, F (max v.1 v.2) = ∑ m ∈ Icc 1 N, hfun m * F m := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : ∑ v ∈ prim 0, F (max v.1 v.2) = 0 := sum_eq_zero (fun v hv => by
      simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hv
      obtain ⟨⟨⟨hv1, hv2⟩, _⟩, _⟩ := hv
      omega)
    have h2 : ∑ m ∈ Icc 1 0, hfun m * F m = 0 := sum_eq_zero (fun m hm => by
      rw [mem_Icc] at hm
      omega)
    rw [h1, h2]
  · have h1 := sum_prim_max N F hN
    have hpt : ∀ m ∈ Icc 1 N,
        hfun m * F m + (if m = 1 then F m else 0) = 2 * (Nat.totient m * F m) := by
      intro m _
      unfold hfun
      split_ifs with h
      · subst h
        rw [Nat.totient_one]
        ring
      · ring
    have h2 : ∑ m ∈ Icc 1 N, hfun m * F m + F 1 = 2 * ∑ m ∈ Icc 1 N, Nat.totient m * F m := by
      have hs : ∑ m ∈ Icc 1 N, (if m = 1 then F m else 0) = F 1 := by
        rw [sum_ite_eq']
        split_ifs with h1N
        · rfl
        · exact absurd (mem_Icc.mpr ⟨le_refl 1, hN⟩) h1N
      rw [← hs, ← sum_add_distrib, mul_sum]
      exact sum_congr rfl hpt
    omega

lemma axis_sum_eval (N : ℕ) :
    ∑ θ ∈ prim N, Lw N (A3v θ) * Iw N (A3v θ) =
      ∑ m ∈ Icc 1 N, hfun m * (N / m * N * ((N / m * N) ^ 2 - Dgrid (N / m) N)) := by
  refine Eq.trans ?_
    (sum_prim_max_h N (fun m => N / m * N * ((N / m * N) ^ 2 - Dgrid (N / m) N)))
  apply sum_congr rfl
  rintro ⟨a, b⟩ hθ
  simp only [prim, rows2, entries, mem_filter, mem_product, mem_Icc] at hθ
  obtain ⟨⟨⟨ha1, _⟩, hb1, _⟩, hc⟩ := hθ
  show _ = N / max a b * N * ((N / max a b * N) ^ 2 - Dgrid (N / max a b) N)
  rw [Lw_A3v_eq, Iw_A3v_eq, axis_card ha1 hb1 hc, IP_axis ha1 hb1 hc]

lemma generic_sum_eval (N : ℕ) :
    ∑ θ ∈ prim3 (N ^ 2), Lw N (G3v θ) * Iw N (G3v θ) =
      ∑ θ ∈ prim3 (N ^ 2), (genRows N θ).card * IP (genRows N θ) := by
  apply sum_congr rfl
  intro θ _
  rw [Lw_G3v_eq, Iw_eq_IP, rowsOn_G3v]

/-! ### Theorem 3.6 -/

/-- **Theorem 3.6** (exact decomposition). With `q_m = ⌊N/m⌋`,
`S₃(N) = N³ ∑_{m ≤ N} g(m) q_m² + 3 ∑_{m ≤ N} h(m) q_m N (q_m² N² - D(q_m, N))
  + 3 ∑_{(a,b,c)} L_{abc} I_{abc}`,
where the last sum runs over primitive triples with `a, b, c ≤ N²` and `L_{abc}`, `I_{abc}` are
`L_P`, `I_P` for the plane `a x + b y = c z`. -/
theorem exact_decomposition (N : ℕ) :
    S3 N = N ^ 3 * ∑ m ∈ Icc 1 N, g3 N m * (N / m) ^ 2 +
      3 * ∑ m ∈ Icc 1 N, hfun m * (N / m * N * ((N / m * N) ^ 2 - Dgrid (N / m) N)) +
      3 * ∑ θ ∈ prim3 (N ^ 2), (genRows N θ).card * IP (genRows N θ) := by
  rw [S3_normals, sum_Wbox_split, axis_sum_reduce, axis_sum_eval, generic_sum_eval,
    A3count_eq_sum_g]
  ring

-- Checks: the right-hand side evaluates to `S₃(2) = 248` and `S₃(3) = 3975` (Appendix A).
example : 2 ^ 3 * ∑ m ∈ Icc 1 2, g3 2 m * (2 / m) ^ 2 +
    3 * ∑ m ∈ Icc 1 2, hfun m * (2 / m * 2 * ((2 / m * 2) ^ 2 - Dgrid (2 / m) 2)) +
    3 * ∑ θ ∈ prim3 (2 ^ 2), (genRows 2 θ).card * IP (genRows 2 θ) = 248 := by
  native_decide

example : 3 ^ 3 * ∑ m ∈ Icc 1 3, g3 3 m * (3 / m) ^ 2 +
    3 * ∑ m ∈ Icc 1 3, hfun m * (3 / m * 3 * ((3 / m * 3) ^ 2 - Dgrid (3 / m) 3)) +
    3 * ∑ θ ∈ prim3 (3 ^ 2), (genRows 3 θ).card * IP (genRows 3 θ) = 3975 := by
  native_decide

end SingularMatrices
