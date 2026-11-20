import «section 7».Lemma720Val

/-! Lemma 7.20: the geometry of the cells of the assembled contraction.

A fibre of the contraction has the form
`cellOf D ε τ = {(x, y) : x ∈ D, rv(y − ε x) = τ}`, with `D` an open disc avoiding `0`,
`τ ≠ 0`, and all second coordinates nonzero. This file shows that such a set satisfies
`TwoCellInput.CellWith` with kind

* `0` when `ε` is constant on `D` (`cellWith_const`);
* `1` when `ε` is in the narrow-image case (`cellWith_narrow`);
* `2` (balanced, second paradigm `t₁ = σ⁻¹ · (rv(−1) · τ)`) when `ε` is injective,
  rv-affine with slope `σ` and disc-to-disc on `D`, and the image disc has radius
  `< vrv τ` (`cellWith_balanced`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells
open DiamondIntegral.Section7.TwoCellInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The translate `c + τ^♯`. -/
def tdisc (c : VF M) (τ : RVInfinity M) : Set (VF M) := {x | rv M (x - c) = τ}

/-- The candidate cell over `D` with positioning function `ε` and paradigm `τ`. -/
def cellOf (D : Set (VF M)) (ε : VF M → VF M) (τ : RVInfinity M) : Set (VF M × VF M) :=
  {p | p.1 ∈ D ∧ rv M (p.2 - ε p.1) = τ}

theorem tdisc_eq_image (c : VF M) (τ : RVInfinity M) : tdisc c τ = (· + c) '' sharpSet τ := by
  ext x
  constructor
  · intro hx
    exact ⟨x - c, hx, sub_add_cancel x c⟩
  · rintro ⟨z, hz, rfl⟩
    change rv M (z + c - c) = τ
    rw [add_sub_cancel_right]
    exact hz

theorem first_cellOf (D : Set (VF M)) (ε : VF M → VF M) (τ : RVInfinity M) :
    first (cellOf D ε τ) = D := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.1
  · intro hx
    obtain ⟨z, hz⟩ := rv_surjective τ
    refine ⟨(x, z + ε x), ⟨hx, ?_⟩, rfl⟩
    change rv M (z + ε x - ε x) = τ
    rw [add_sub_cancel_right]
    exact hz

theorem fibre_cellOf (D : Set (VF M)) (ε : VF M → VF M) (τ : RVInfinity M) {a : VF M} (ha : a ∈ D) :
    fibre (cellOf D ε τ) a = (· + ε a) '' sharpSet τ := by
  rw [← tdisc_eq_image]
  ext y
  exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩

theorem second_cellOf (D : Set (VF M)) (ε : VF M → VF M) (τ : RVInfinity M) :
    second (cellOf D ε τ) = ⋃ a ∈ D, tdisc (ε a) τ := by
  ext y
  simp only [second, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp.1, hp.2⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨(a, y), ⟨ha, hy⟩, rfl⟩

theorem rvZero_eq_zero : rvZero M = 0 := by
  rw [← rv_zero]
  exact map_zero RVOperations.rvHom

theorem rv_neg_one_sq : rv M (-1) * rv M (-1) = 1 := by
  rw [← rv_mul_eq, neg_one_mul, neg_neg]
  change RVOperations.rvHom 1 = 1
  exact map_one _

theorem rv_sub_swap (x a : VF M) : rv M (a - x) = rv M (-1) * rv M (x - a) := by
  rw [← rv_mul_eq]
  congr 1
  ring

/-- The value of a nonzero element, as an element of `Γ`. -/
def gval (z : VF M) (hz : z ≠ 0) : Gamma M := finiteValue z hz

theorem gval_val (z : VF M) (hz : z ≠ 0) : (gval z hz).val = vfValue z := rfl

section Discs
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
include hv

theorem mem_disc_iff {D : Set (VF M)} {a : VF M} {γ : Gamma M}
    (h : Subtype.val '' D = BallImaginaries.underlying (openDiscCode a γ)) (x : VF M) :
    x ∈ D ↔ γ.val < vfValue (x - a) := by
  rw [← openDiscCode_mem_iff_value, ← h]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => Subtype.ext he ▸ hy⟩

theorem disc_of_mem_iff {D : Set (VF M)} {a : VF M} {γ : Gamma M}
    (h : ∀ x : VF M, x ∈ D ↔ γ.val < vfValue (x - a)) :
    Subtype.val '' D = BallImaginaries.underlying (openDiscCode a γ) := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (openDiscCode_mem_iff_value a x γ).mpr ((h x).mp hx)
  · intro hm
    let x : VF M := ⟨m, disc_underlying_subset_vf _ hm⟩
    exact ⟨x, (h x).mpr ((openDiscCode_mem_iff_value a x γ).mp hm), rfl⟩

/-- `c + τ^♯` is the open disc of radius `vfValue z` around `c + z`, for `rv z = τ ≠ 0`. -/
theorem tdisc_mem_iff (c z : VF M) (hz : z ≠ 0) (x : VF M) :
    x ∈ tdisc c (rv M z) ↔ (gval z hz).val < vfValue (x - (c + z)) := by
  rw [gval_val]
  change rv M (x - c) = rv M z ↔ _
  rw [rv_eq_iff_value_close hz]
  have he : x - c - z = x - (c + z) := by ring
  rw [he]

theorem tdisc_isOpenDisc (c : VF M) {τ : RVInfinity M} (hτ : τ ≠ rvZero M) :
    IsOpenDiscVF (tdisc c τ) := by
  obtain ⟨z, rfl⟩ := rv_surjective τ
  have hz : z ≠ 0 := fun h => hτ (by rw [h, rv_zero])
  exact ⟨c + z, gval z hz, disc_of_mem_iff hv (tdisc_mem_iff hv c z hz)⟩

/-- Translates of `τ^♯` by close centres agree. -/
theorem tdisc_eq_of_close {c c' z : VF M} (hz : z ≠ 0) (hclose : vfValue z < vfValue (c - c')) :
    tdisc c (rv M z) = tdisc c' (rv M z) := by
  ext x
  change rv M (x - c) = rv M z ↔ rv M (x - c') = rv M z
  constructor
  · intro h
    have hxc : x - c ≠ 0 := fun h0 => hz ((rv_eq_zero_iff z).mp (h ▸ (by rw [h0, rv_zero])))
    rw [← h]
    apply rv_eq_of_value_close hxc
    rw [vfValue_eq_of_rv_eq h]
    have he : x - c' - (x - c) = c - c' := by ring
    rw [he]
    exact hclose
  · intro h
    have hxc : x - c' ≠ 0 := fun h0 => hz ((rv_eq_zero_iff z).mp (h ▸ (by rw [h0, rv_zero])))
    rw [← h]
    apply rv_eq_of_value_close hxc
    rw [vfValue_eq_of_rv_eq h]
    have he : x - c - (x - c') = -(c - c') := by ring
    rw [he, vfValue_neg hv]
    exact hclose

/-- An open disc avoiding `0` lies in a single RV-disc. -/
theorem rv_const_of_disc {D : Set (VF M)} (hD : IsOpenDiscVF D) (h0 : (0 : VF M) ∉ D) {x x' : VF M}
    (hx : x ∈ D) (hx' : x' ∈ D) : rv M x' = rv M x := by
  obtain ⟨a, γ, hγ⟩ := hD
  have hxa := (mem_disc_iff hv hγ x).mp hx
  have hx'a := (mem_disc_iff hv hγ x').mp hx'
  have h0a : ¬ γ.val < vfValue (0 - a) := fun h => h0 ((mem_disc_iff hv hγ 0).mpr h)
  rw [zero_sub, vfValue_neg hv, not_lt] at h0a
  have hxx : γ.val < vfValue (x' - x) := by
    have he : x' - x = (x' - a) + -(x - a) := by ring
    rw [he]
    exact lt_vfValue_add hv hx'a (by rw [vfValue_neg hv]; exact hxa)
  have hvx : vfValue x = vfValue a := by
    have he : x = (x - a) + a := by ring
    rw [he, add_comm, vfValue_add_eq_of_lt hv (lt_of_le_of_lt h0a hxa)]
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  apply rv_eq_of_value_close hx0
  rw [hvx]
  exact lt_of_le_of_lt h0a hxx

/-- The RV-polydisc clause and the `1`-cell clause of a cell over an open disc avoiding
`0`, whose second projection is an open disc avoiding `0`. -/
theorem polydisc_clause {D : Set (VF M)} (hD : IsOpenDiscVF D) (hD0 : (0 : VF M) ∉ D)
    {ε : VF M → VF M} {τ : RVInfinity M}
    (hY : IsOpenDiscVF (second (cellOf D ε τ))) (hY0 : (0 : VF M) ∉ second (cellOf D ε τ)) :
    (∃ u₁ u₂ : RVInfinity M, ∀ p ∈ cellOf D ε τ, rv M p.1 = u₁ ∧ rv M p.2 = u₂) ∧
      IsOneCell (first (cellOf D ε τ)) := by
  rw [first_cellOf]
  refine ⟨?_, ?_⟩
  · by_cases hne : (cellOf D ε τ).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      refine ⟨rv M p₀.1, rv M p₀.2, fun p hp => ⟨?_, ?_⟩⟩
      · exact rv_const_of_disc hv hD hD0 hp₀.1 hp.1
      · exact rv_const_of_disc hv hY hY0 ⟨p₀, hp₀, rfl⟩ ⟨p, hp, rfl⟩
    · refine ⟨rvZero M, rvZero M, fun p hp => (hne ⟨p, hp⟩).elim⟩
  · refine Or.inr ⟨hD, ?_⟩
    by_cases hne : D.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      exact ⟨rv M x₀, fun x hx => rv_const_of_disc hv hD hD0 hx₀ hx⟩
    · exact ⟨rvZero M, fun x hx => (hne ⟨x, hx⟩).elim⟩

theorem zero_not_mem_second {D : Set (VF M)} {ε : VF M → VF M} {τ : RVInfinity M}
    (hY : ∀ p ∈ cellOf D ε τ, p.2 ≠ 0) : (0 : VF M) ∉ second (cellOf D ε τ) := by
  rintro ⟨p, hp, h⟩
  exact hY p hp h

/-- If all translates over `D` agree, the second projection is one of them. -/
theorem second_eq_of_translates {D : Set (VF M)} {ε : VF M → VF M} {τ : RVInfinity M} {a₀ : VF M}
    (ha₀ : a₀ ∈ D) (hall : ∀ a ∈ D, tdisc (ε a) τ = tdisc (ε a₀) τ) :
    second (cellOf D ε τ) = tdisc (ε a₀) τ := by
  rw [second_cellOf]
  ext y
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hy⟩
    rw [← hall a ha]
    exact hy
  · intro hy
    exact ⟨a₀, ha₀, hy⟩

/-- **Kind 0**: constant positioning function. -/
theorem cellWith_const {D : Set (VF M)} (hD : IsOpenDiscVF D) (hD0 : (0 : VF M) ∉ D)
    {ε : VF M → VF M} {τ : RV M} (hY : ∀ p ∈ cellOf D ε τ.val, p.2 ≠ 0)
    (hconst : ∀ a ∈ D, ∀ a' ∈ D, ε a = ε a') (t₁ : RVInfinity M) :
    CellWith (cellOf D ε τ.val) ε τ t₁ 0 := by
  have hfib : ∀ a ∈ first (cellOf D ε τ.val), fibre (cellOf D ε τ.val) a = (· + ε a) '' sharpSet τ.val := by
    intro a ha
    rw [first_cellOf] at ha
    exact fibre_cellOf D ε τ.val ha
  by_cases hne : D.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    have hsec := second_eq_of_translates hv (ε := ε) (τ := τ.val) ha₀ (fun a ha => by rw [hconst a ha a₀ ha₀])
    have hY' : IsOpenDiscVF (second (cellOf D ε τ.val)) := by
      rw [hsec]
      exact tdisc_isOpenDisc hv _ τ.property
    obtain ⟨h1, h2⟩ := polydisc_clause hv hD hD0 hY' (zero_not_mem_second hv hY)
    refine ⟨h1, h2, hfib, fun _ a ha a' ha' => ?_, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
    rw [first_cellOf] at ha ha'
    exact hconst a ha a' ha'
  · have hD' : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨?_, ?_, hfib, fun _ a ha => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    · exact ⟨rvZero M, rvZero M, fun p hp => by rw [hD'] at hp; exact hp.1.elim⟩
    · rw [first_cellOf]; exact Or.inr ⟨hD, rvZero M, fun x hx => by rw [hD'] at hx; exact hx.elim⟩
    · rw [first_cellOf, hD'] at ha; exact ha.elim

/-- **Kind 1**: the narrow-image case. -/
theorem cellWith_narrow {D : Set (VF M)} (hD : IsOpenDiscVF D) (hD0 : (0 : VF M) ∉ D)
    {ε : VF M → VF M} {τ : RV M} (hY : ∀ p ∈ cellOf D ε τ.val, p.2 ≠ 0)
    (hN : NarrowCase (cellOf D ε τ.val) ε τ) (t₁ : RVInfinity M) :
    CellWith (cellOf D ε τ.val) ε τ t₁ 1 := by
  have hfib : ∀ a ∈ first (cellOf D ε τ.val), fibre (cellOf D ε τ.val) a = (· + ε a) '' sharpSet τ.val := by
    intro a ha
    rw [first_cellOf] at ha
    exact fibre_cellOf D ε τ.val ha
  obtain ⟨-, -, x, γ, himg, hγ⟩ := id hN
  rw [first_cellOf] at himg
  obtain ⟨z, hz⟩ := rv_surjective τ.val
  have hz0 : z ≠ 0 := fun h => τ.property (by rw [← hz, h, rv_zero])
  have hclose : ∀ a ∈ D, ∀ a' ∈ D, vfValue z < vfValue (ε a - ε a') := by
    intro a ha a' ha'
    have h1 := (mem_disc_iff hv himg (ε a)).mp ⟨a, ha, rfl⟩
    have h2 := (mem_disc_iff hv himg (ε a')).mp ⟨a', ha', rfl⟩
    have hzγ : vfValue z ≤ γ.val := by
      change Values.vrv (rv M z) ≤ γ.val
      rw [hz]
      exact hγ
    refine lt_of_le_of_lt hzγ ?_
    have he : ε a - ε a' = (ε a - x) + -(ε a' - x) := by ring
    rw [he]
    exact lt_vfValue_add hv h1 (by rw [vfValue_neg hv]; exact h2)
  by_cases hne : D.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    have hsec := second_eq_of_translates hv (τ := τ.val) ha₀ (fun a ha => by
      rw [← hz]
      exact tdisc_eq_of_close hv hz0 (hclose a ha a₀ ha₀))
    have hY' : IsOpenDiscVF (second (cellOf D ε τ.val)) := by
      rw [hsec]
      exact tdisc_isOpenDisc hv _ τ.property
    obtain ⟨h1, h2⟩ := polydisc_clause hv hD hD0 hY' (zero_not_mem_second hv hY)
    exact ⟨h1, h2, hfib, fun h => absurd h (by decide), fun _ => hN, fun h => absurd h (by decide)⟩
  · have hD' : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨?_, ?_, hfib, fun h => absurd h (by decide), fun _ => hN, fun h => absurd h (by decide)⟩
    · exact ⟨rvZero M, rvZero M, fun p hp => by rw [hD'] at hp; exact hp.1.elim⟩
    · rw [first_cellOf]; exact Or.inr ⟨hD, rvZero M, fun x hx => by rw [hD'] at hx; exact hx.elim⟩

/-- Two points of an open disc are closer than its radius. -/
theorem lt_of_mem_disc {D : Set (VF M)} {d : VF M} {γ : Gamma M}
    (h : Subtype.val '' D = BallImaginaries.underlying (openDiscCode d γ)) {x x' : VF M}
    (hx : x ∈ D) (hx' : x' ∈ D) : γ.val < vfValue (x - x') := by
  have h1 := (mem_disc_iff hv h x).mp hx
  have h2 := (mem_disc_iff hv h x').mp hx'
  have he : x - x' = (x - d) + -(x' - d) := by ring
  rw [he]
  exact lt_vfValue_add hv h1 (by rw [vfValue_neg hv]; exact h2)

/-- A point at distance beyond the radius from a point of an open disc is in it. -/
theorem mem_disc_of_close {D : Set (VF M)} {d : VF M} {γ : Gamma M}
    (h : Subtype.val '' D = BallImaginaries.underlying (openDiscCode d γ)) {x z : VF M}
    (hx : x ∈ D) (hz : γ.val < vfValue z) : x + z ∈ D := by
  apply (mem_disc_iff hv h _).mpr
  have he : x + z - d = (x - d) + z := by ring
  rw [he]
  exact lt_vfValue_add hv ((mem_disc_iff hv h x).mp hx) hz

/-- **Kind 2**: the balanced case. -/
theorem cellWith_balanced {D : Set (VF M)} (hD : IsOpenDiscVF D) (hD0 : (0 : VF M) ∉ D)
    {ε : VF M → VF M} {τ : RV M} (hY : ∀ p ∈ cellOf D ε τ.val, p.2 ≠ 0)
    (hinj : Set.InjOn ε D) (hd2d : DiscToDisc D ε) {σ : RV M} (hslope : HasSlope D ε σ)
    {e : VF M} {γ : Gamma M} (himg : Subtype.val '' (ε '' D) = BallImaginaries.underlying (openDiscCode e γ))
    (hγ : γ.val < Values.vrv τ.val) :
    CellWith (cellOf D ε τ.val) ε τ (σ.val⁻¹ * (rv M (-1) * τ.val)) 2 := by
  have hfib : ∀ a ∈ first (cellOf D ε τ.val), fibre (cellOf D ε τ.val) a = (· + ε a) '' sharpSet τ.val := by
    intro a ha
    rw [first_cellOf] at ha
    exact fibre_cellOf D ε τ.val ha
  obtain ⟨z₀, hz₀⟩ := rv_surjective τ.val
  have hz₀γ : γ.val < vfValue z₀ := by
    change γ.val < Values.vrv (rv M z₀)
    rw [hz₀]
    exact hγ
  have hsec : second (cellOf D ε τ.val) = ε '' D := by
    rw [second_cellOf]
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hy⟩
      have hya : y = ε a + (y - ε a) := by ring
      rw [hya]
      apply mem_disc_of_close hv himg ⟨a, ha, rfl⟩
      change γ.val < Values.vrv (rv M (y - ε a))
      rw [show rv M (y - ε a) = τ.val from hy]
      exact hγ
    · rintro ⟨x', hx', rfl⟩
      have hw : ε x' + -z₀ ∈ ε '' D :=
        mem_disc_of_close hv himg ⟨x', hx', rfl⟩ (by rw [vfValue_neg hv]; exact hz₀γ)
      obtain ⟨x, hx, hxe⟩ := hw
      refine ⟨x, hx, ?_⟩
      change rv M (ε x' - ε x) = τ.val
      rw [hxe]
      have he : ε x' - (ε x' + -z₀) = z₀ := by ring
      rw [he, hz₀]
  have hdiscImg : IsOpenDiscVF (ε '' D) := ⟨e, γ, himg⟩
  have hY' : IsOpenDiscVF (second (cellOf D ε τ.val)) := by rw [hsec]; exact hdiscImg
  obtain ⟨h1, h2⟩ := polydisc_clause hv hD hD0 hY' (zero_not_mem_second hv hY)
  have hσ0 : σ.val ≠ 0 := by rw [← rvZero_eq_zero]; exact σ.property
  -- the preimage computation, forward direction
  have hfwd : ∀ a ∈ D, ∀ x ∈ D, rv M (ε x - ε a) = τ.val →
      rv M (a - x) = σ.val⁻¹ * (rv M (-1) * τ.val) := by
    intro a ha x hx h
    have hs := hslope x hx a ha
    rw [h] at hs
    rw [rv_sub_swap, hs, mul_left_comm (rv M (-1)) σ.val, inv_mul_cancel_left₀ hσ0]
  refine ⟨h1, h2, hfib, fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hfib, ?_⟩
  · rw [first_cellOf]; exact hD
  · rw [hsec]; exact hdiscImg
  · rw [first_cellOf, hsec]; exact hinj.bijOn_image
  · rw [first_cellOf]; exact hd2d
  · rw [first_cellOf]; exact ⟨hD, hinj, σ, hslope⟩
  · intro a ha
    rw [first_cellOf] at ha ⊢
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨hxf, hx⟩
      refine ⟨a - x, ?_, sub_sub_cancel a x⟩
      exact hfwd a ha x hx hxf.2
    · rintro ⟨z, hz, rfl⟩
      -- a point of `D` at the same distance as `z`
      have hy : ε a + z₀ ∈ second (cellOf D ε τ.val) := by
        rw [second_cellOf]
        simp only [Set.mem_iUnion]
        refine ⟨a, ha, ?_⟩
        change rv M (ε a + z₀ - ε a) = τ.val
        rw [add_sub_cancel_left, hz₀]
      rw [hsec] at hy
      obtain ⟨x', hx', hx'e⟩ := hy
      have hx'rv : rv M (a - x') = σ.val⁻¹ * (rv M (-1) * τ.val) := by
        apply hfwd a ha x' hx'
        rw [hx'e, add_sub_cancel_left, hz₀]
      obtain ⟨d, γD, hdisc⟩ := hD
      have hD' := lt_of_mem_disc hv hdisc ha hx'
      have hvz : vfValue (a - x') = vfValue z := by
        change Values.vrv (rv M (a - x')) = Values.vrv (rv M z)
        change rv M z = _ at hz
        rw [hx'rv, hz]
      have hxD : a - z ∈ D := by
        have he : a - z = a + -z := sub_eq_add_neg a z
        rw [he]
        exact mem_disc_of_close hv hdisc ha (by rw [vfValue_neg hv, ← hvz]; exact hD')
      refine ⟨⟨ha, ?_⟩, hxD⟩
      change rv M (ε (a - z) - ε a) = τ.val
      rw [hslope (a - z) hxD a ha]
      change rv M z = _ at hz
      have he : a - z - a = (-1) * z := by ring
      rw [he, rv_mul_eq, hz, mul_left_comm (rv M (-1)) σ.val⁻¹, mul_inv_cancel_left₀ hσ0, ← mul_assoc,
        rv_neg_one_sq, one_mul]

/-- The kind of a cell: `0` if `ε` is constant on `D`, `1` if all translates agree,
`2` otherwise. -/
def kindOf (D : Set (VF M)) (ε : VF M → VF M) (τ : RV M) : Fin 3 :=
  if ∀ a ∈ D, ∀ a' ∈ D, ε a = ε a' then 0
  else if ∀ a ∈ D, ∀ a' ∈ D, Values.vrv τ.val < vfValue (ε a - ε a') then 1 else 2

/-- **The cell classification.** If `ε` is constant on `D`, or injective, rv-affine and
disc-to-disc on `D`, then the cell over `D` satisfies Definition 7.19 with kind `kindOf`. -/
theorem cellWith_kindOf {D : Set (VF M)} (hD : IsOpenDiscVF D) (hD0 : (0 : VF M) ∉ D)
    {ε : VF M → VF M} {τ : RV M} (hY : ∀ p ∈ cellOf D ε τ.val, p.2 ≠ 0) {σ : RV M}
    (hcase : (∀ a ∈ D, ∀ a' ∈ D, ε a = ε a') ∨
      (Set.InjOn ε D ∧ DiscToDisc D ε ∧ HasSlope D ε σ)) :
    CellWith (cellOf D ε τ.val) ε τ (σ.val⁻¹ * (rv M (-1) * τ.val)) (kindOf D ε τ) := by
  by_cases hc : ∀ a ∈ D, ∀ a' ∈ D, ε a = ε a'
  · rw [kindOf, if_pos hc]
    exact cellWith_const hv hD hD0 hY hc _
  · obtain ⟨hinj, hd2d, hslope⟩ := hcase.resolve_left hc
    rw [kindOf, if_neg hc]
    obtain ⟨e, γ, himg⟩ := hd2d D le_rfl hD
    by_cases hn : ∀ a ∈ D, ∀ a' ∈ D, Values.vrv τ.val < vfValue (ε a - ε a')
    · rw [if_pos hn]
      refine cellWith_narrow hv hD hD0 hY ⟨by rw [first_cellOf]; exact hinj,
        by rw [first_cellOf]; exact hd2d, e, γ, by rw [first_cellOf]; exact himg, ?_⟩ _
      -- the radius of the image is at least `vrv τ`
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨z₀, hz₀⟩ := rv_surjective τ.val
      have hz₀γ : γ.val < vfValue z₀ := by
        change γ.val < Values.vrv (rv M z₀)
        rw [hz₀]
        exact hlt
      by_cases hDne : D.Nonempty
      · obtain ⟨a, ha⟩ := hDne
        have hw : ε a + z₀ ∈ ε '' D := mem_disc_of_close hv himg ⟨a, ha, rfl⟩ hz₀γ
        obtain ⟨a', ha', he⟩ := hw
        have h := hn a' ha' a ha
        rw [he, add_sub_cancel_left] at h
        change Values.vrv τ.val < Values.vrv (rv M z₀) at h
        rw [hz₀] at h
        exact lt_irrefl _ h
      · obtain ⟨d, γD, hdisc⟩ := hD
        obtain ⟨u, hu⟩ := (show (BallImaginaries.underlying (openDiscCode d γD)).Nonempty from by
          refine ⟨d.val, (openDiscCode_mem_iff_value d d γD).mpr ?_⟩
          rw [sub_self]
          exact SpecialTransformations.Section9.gamma_lt_value_zero γD)
        rw [← hdisc] at hu
        obtain ⟨x, hx, -⟩ := hu
        exact hDne ⟨x, hx⟩
    · rw [if_neg hn]
      apply cellWith_balanced hv hD hD0 hY hinj hd2d hslope himg
      by_contra hge
      rw [not_lt] at hge
      apply hn
      intro a ha a' ha'
      exact lt_of_le_of_lt hge (lt_of_mem_disc hv himg ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩)

end Discs

end DiamondIntegral.Section7.Lemma720
