import «section 6».MeasuredRVLiftingInductionStep
import Section9.MixedDifferentiationAE

/-! One original-base VF-small set removes the nondifferentiability
loci of any finite family of actual mixed maps, simultaneously across
every old RV label. All derivatives are full total derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_uniform_mixed_differentiability_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)
    {I : Type} [Finite I] (s : I → ℕ) (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : ∀ i, DefSet (rawMixedSpace (M := M) n (s i)) S) (f : ∀ i, Map A (B i)) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → ∀ i, ∃ L, HasMixedVFDerivativeAt (f i) p L := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let C (i : I) : DefSet (rawMixedSpace (M := M) n r) S :=
    ⟨{x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt (f i) p L},
      mixedDifferentiabilityLocus_definable hn (f i)⟩
  let H := finiteDefSetIntersection A C
  let E := A.sdiff H
  refine ⟨E,Set.sdiff_subset,?_,?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) hn E
    intro p hp
    let q : A := ⟨p.val,p.property.1⟩
    apply p.property.2
    exact ⟨q.property,fun i => ⟨q,rfl,mixedDifferentiableAt_of_independent hc hκ hs hsmall hv (f i) q hp⟩⟩
  · intro p hp i
    have hH : p.val ∈ H.carrier := by
      by_contra h
      exact hp ⟨p.property,h⟩
    obtain ⟨q,hq,L,hL⟩ := hH.2 i
    have he : q = p := Subtype.ext hq
    subst q
    exact ⟨L,hL⟩

theorem exists_small_rv_labels_for_mixed_differentiability
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : MeasuredRVObject (M := M) S (n+1)) {I : Type} [Finite I] (s : I → ℕ)
    (B : ∀ i, DefSet (rawMixedSpace (M := M) (n+1) (s i)) S)
    (f : ∀ i, Map (rvLift U.object) (B i)) :
    ∃ D : DefSet (rawRVSpace (M := M) U.object.arity) S, D.carrier ⊆ U.object.domain.carrier ∧
      rvDim D < n+1 ∧ ∀ p : rvLift U.object, p.val.2 ∉ D.carrier →
        ∀ i, ∃ L, HasMixedVFDerivativeAt (f i) p L := by
  obtain ⟨E,hE,hDim,hGood⟩ := exists_uniform_mixed_differentiability_exception h00 hc hκ hs hsmall hv
    (Nat.zero_lt_succ n) s (rvLift U.object) B f
  let D := badRVLiftLabels U.object E hE
  refine ⟨D,badRVLiftLabels_subset U.object E hE,
    badRVLiftLabels_dimension_drop hc h00 hκ hs hsmall hΓ hv U.object U.finiteVolume U.nonzero E hE hDim,?_⟩
  intro p hp i
  apply hGood p ?_ i
  intro hpE
  exact hp ⟨⟨p.val,hpE⟩,rfl⟩

end DiamondIntegral.Section6
