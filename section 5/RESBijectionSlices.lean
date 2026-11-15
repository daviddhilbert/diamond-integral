import «section 5».RESForwardScissors

/-! Finite source/target value-pattern refinements of the entire defining
graph of an original-base bijection. Slices and their actual images are
definable over exactly the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance resBijectionSlicesStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]
variable {n m : ℕ}
    {A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c}}
    {B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c}}

def rvMapSlice (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} where
  carrier := (patternPiece A p).carrier ∩ {r | ∃ u : A, u.val = r ∧ (f u).val ∈ (patternPiece B q).carrier}
  definable := Space.Definable.inter _ (patternPiece A p).definable
    (f.definable_preimage (patternPiece B q).definable)

theorem rvMapSlice_mem (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ)
    (r : Fin n → CanonicalRV.RVSort Carrier) :
    r ∈ (rvMapSlice f p q).carrier ↔
      ∃ u : A, u.val = r ∧ valuePattern u.val = p ∧ valuePattern (f u).val = q := by
  constructor
  · rintro ⟨hr, u, hu, hv⟩
    have hs := (patternPiece_mem_iff A p r).mp hr
    have ht := (patternPiece_mem_iff B q (f u).val).mp hv
    exact ⟨u, hu, hu ▸ hs.2, ht.2⟩
  · rintro ⟨u, rfl, hp, hq⟩
    exact ⟨(patternPiece_mem_iff A p u.val).mpr ⟨u.property, hp⟩,
      u, rfl, (patternPiece_mem_iff B q (f u).val).mpr ⟨(f u).property, hq⟩⟩

theorem rvMapSlice_subset (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    (rvMapSlice f p q).carrier ⊆ A.carrier := by
  rintro r hr
  obtain ⟨u, rfl, _, _⟩ := (rvMapSlice_mem f p q r).mp hr
  exact u.property

def rvSliceMap (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    Map (rvMapSlice f p q) B := f.restrict (rvMapSlice_subset f p q)

def rvSliceImage (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :=
  (rvSliceMap f p q).image

theorem rvSliceImage_mem (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ)
    (r : Fin m → CanonicalRV.RVSort Carrier) :
    r ∈ (rvSliceImage f p q).carrier ↔
      ∃ u : A, (f u).val = r ∧ valuePattern u.val = p ∧ valuePattern (f u).val = q := by
  constructor
  · rintro ⟨x, rfl⟩
    let u : A := ⟨x.val, rvMapSlice_subset f p q x.property⟩
    obtain ⟨v, hv, hp, hq⟩ := (rvMapSlice_mem f p q x.val).mp x.property
    have he : v = u := Subtype.ext hv
    subst v
    exact ⟨u, rfl, hp, hq⟩
  · rintro ⟨u, hu, hp, hq⟩
    let x : rvMapSlice f p q := ⟨u.val, (rvMapSlice_mem f p q u.val).mpr ⟨u, rfl, hp, hq⟩⟩
    exact ⟨x, hu⟩

theorem rvMapSlice_support (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    RationalFrameSupport (valuePatternWeights p) (rvMapSlice f p q) :=
  fun r hr => patternPiece_rationalSupport A p r hr.1

theorem rvSliceImage_support (f : Map A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    RationalFrameSupport (valuePatternWeights q) (rvSliceImage f p q) := by
  intro r hr
  obtain ⟨u, rfl, _, hq⟩ := (rvSliceImage_mem f p q r).mp hr
  exact patternPiece_rationalSupport B q _ ((patternPiece_mem_iff B q _).mpr ⟨(f u).property, hq⟩)

def rvSliceBijection (f : DefinableBijection A B) (p : Fin n → WithTop ℚ) (q : Fin m → WithTop ℚ) :
    DefinableBijection (rvMapSlice f.map p q) (rvSliceImage f.map p q) where
  map := (rvSliceMap f.map p q).toImage
  bijective := by
    constructor
    · intro x y he
      have hv : f.map ⟨x.val, rvMapSlice_subset f.map p q x.property⟩ =
          f.map ⟨y.val, rvMapSlice_subset f.map p q y.property⟩ :=
        Subtype.ext (congrArg (fun z : rvSliceImage f.map p q => z.val) he)
      exact Subtype.ext (congrArg (fun z : A => z.val) (f.bijective.injective hv))
    · rintro ⟨_, x, rfl⟩
      exact ⟨x, rfl⟩

theorem rvMapSlice_partition (f : Map A B) (p : Fin n → WithTop ℚ)
    (s : Finset (Fin m → WithTop ℚ)) (hs : actualValuePatterns B ⊆ (s : Set _)) :
    (Pairwise (fun i j : s => Disjoint (rvMapSlice f p i.val).carrier (rvMapSlice f p j.val).carrier)) ∧
      ∀ r, r ∈ (patternPiece A p).carrier ↔ ∃ i : s, r ∈ (rvMapSlice f p i.val).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro r hi hj
    obtain ⟨u, hu, _, hqi⟩ := (rvMapSlice_mem f p i.val r).mp hi
    obtain ⟨v, hv, _, hqj⟩ := (rvMapSlice_mem f p j.val r).mp hj
    have he : u = v := Subtype.ext (hu.trans hv.symm)
    subst v
    exact hij (Subtype.ext (hqi.symm.trans hqj))
  · intro r
    constructor
    · intro hr
      obtain ⟨ha, hp⟩ := (patternPiece_mem_iff A p r).mp hr
      let u : A := ⟨r, ha⟩
      let q := valuePattern (f u).val
      have hq : q ∈ s := hs ⟨f u, rfl⟩
      exact ⟨⟨q, hq⟩, (rvMapSlice_mem f p q r).mpr ⟨u, rfl, hp, rfl⟩⟩
    · rintro ⟨i, hi⟩
      exact hi.1

theorem rvSliceImage_partition (f : DefinableBijection A B) (q : Fin m → WithTop ℚ)
    (s : Finset (Fin n → WithTop ℚ)) (hs : actualValuePatterns A ⊆ (s : Set _)) :
    (Pairwise (fun i j : s => Disjoint (rvSliceImage f.map i.val q).carrier (rvSliceImage f.map j.val q).carrier)) ∧
      ∀ r, r ∈ (patternPiece B q).carrier ↔ ∃ i : s, r ∈ (rvSliceImage f.map i.val q).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro r hi hj
    obtain ⟨u, hu, hpi, _⟩ := (rvSliceImage_mem f.map i.val q r).mp hi
    obtain ⟨v, hv, hpj, _⟩ := (rvSliceImage_mem f.map j.val q r).mp hj
    have he : u = v := f.bijective.injective (Subtype.ext (hu.trans hv.symm))
    subst v
    exact hij (Subtype.ext (hpi.symm.trans hpj))
  · intro r
    constructor
    · intro hr
      obtain ⟨hb, hq⟩ := (patternPiece_mem_iff B q r).mp hr
      obtain ⟨u, hu⟩ := f.bijective.surjective ⟨r, hb⟩
      let p := valuePattern u.val
      have hp : p ∈ s := hs ⟨u, rfl⟩
      have hv : (f.map u).val = r := congrArg Subtype.val hu
      exact ⟨⟨p, hp⟩, (rvSliceImage_mem f.map p q r).mpr ⟨u, hv, rfl, by rwa [hv]⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨u, rfl, _, hq⟩ := (rvSliceImage_mem f.map i.val q r).mp hi
      exact (patternPiece_mem_iff B q _).mpr ⟨(f.map u).property, hq⟩

end DiamondIntegral.Section5.PuiseuxOriginal
