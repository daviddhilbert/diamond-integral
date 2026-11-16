import «section 6».UnaryMeasuredPreparation

/-! A finite proper invariant cover gives a proper ambient, and proper
Gamma levels on its pieces give open global levels. Disjointness is not
needed for these implications. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ} {S : Set M}

theorem properInvariant_of_finite_cover
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier) : ProperInvariant S A.carrier := by
  let α (i : Fin k) := (hC i).vfBounded.choose
  let β (i : Fin k) := (hC i).rvBounded.choose
  obtain ⟨a,ha⟩ := (Set.finite_range α).bddBelow
  obtain ⟨b,hb⟩ := (Set.finite_range β).bddAbove
  have hVF : VFBounded A.carrier := by
    refine ⟨a,fun p hp j => ?_⟩
    obtain ⟨i,hi⟩ := hCover p hp
    have hLower : a.val ≤ (α i).val := ha (Set.mem_range_self i)
    exact hLower.trans ((hC i).vfBounded.choose_spec p hi j)
  have hRV : RVSupportDoublyBounded A.carrier := by
    refine ⟨b,fun p hp j => ?_⟩
    obtain ⟨i,hi⟩ := hCover p hp
    have hβ : β i ≤ b := hb (Set.mem_range_self i)
    have hVal := (hC i).rvBounded.choose_spec p hi j
    exact ⟨(show (b⁻¹).val ≤ ((β i)⁻¹).val from inv_le_inv' hβ).trans hVal.1,hVal.2.trans hβ⟩
  apply (lemma_6_5 h00 hc hκ hs hv A.carrier A.definable hVF hRV).mpr
  intro u
  have hEq : vfFibre A.carrier u = ⋃ i, vfFibre (C i).carrier u := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := hCover (x,u) hx
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact hCA i hi
  rw [hEq]
  exact isClopen_iUnion_of_finite (fun i => (hC i).clopen_fibres hv u)

theorem gamma_levels_open_of_finite_cover
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M n r → Gamma M)
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ ω (a,u) = γ} := by
  intro u γ
  have hEq : {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ ω (a,u) = γ} =
      ⋃ i, vfFibre {p | p ∈ (C i).carrier ∧ ω p = γ} u := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      obtain ⟨i,hi⟩ := hCover (x,u) hx
      exact Set.mem_iUnion.mpr ⟨i,hi,hγ⟩
    · intro hx
      obtain ⟨i,hi,hγ⟩ := Set.mem_iUnion.mp hx
      exact ⟨hCA i hi,hγ⟩
  rw [hEq]
  exact isOpen_iUnion (fun i => ((hLevels i γ).clopen_fibres hv u).isOpen)

end DiamondIntegral.Section6
