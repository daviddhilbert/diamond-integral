import «section 6».MeasuredVFBadLabelRepair
import «section 6».MeasuredVFChainComponentAssembly
import «section 6».OriginalBaseRelativeMeasuredRVLifting
import «section 6».RVIsomorphismFactorizations

/-! The full-degree step for measured VF unary chains. The generic
relative lift and the actual RV-boundary dimension drop reduce every
exceptional-label chain to strictly smaller RV rank. No lifting theorem
is accepted as a background input: the smaller-rank premise is the
explicit induction hypothesis to be discharged by rank induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_relative_measured_vf_chain_of_smaller_ranks_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) (n+1)} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < n+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) (n+1) P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    {U V : MeasuredRVObject (M := M) (S : Set M) (n+1)} (e : MeasuredRVIso U V)
    (active : Fin (n+1)) (hRelative : RVUnaryRelativeAt e.iso.hom.map active) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) (n+1) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  obtain ⟨f,hf,hUnary,hlabel,E,hE,hDim,hGood⟩ := exists_relative_measured_rv_lift_ae_vfGenerated
    h00 hc hκ hs hv S B hsmall (Nat.zero_lt_succ n) e active hRelative
  let D := badRVLiftLabels U.object E hE
  let hD := badRVLiftLabels_subset U.object E hE
  have hSmall : rvDim D < n+1 := badRVLiftLabels_dimension_drop hc h00 hκ.le hs hsmall hΓ hv
    U.object U.finiteVolume U.nonzero E hE hDim
  obtain ⟨T,hT,hTB⟩ := hLower (e.restrict D hD) hSmall
  exact exists_repaired_relative_measured_vf_chain hc (Nat.zero_lt_succ n) e f hf hlabel active hUnary D hD T hT
    (fun hB => hTB ⟨U.restrict_doublyBounded _ _ hB.1,V.restrict_doublyBounded _ _ hB.2⟩)
    (fun p hp => hGood p (by
      intro hpE
      exact hp (⟨⟨p.val,hpE⟩,rfl⟩ : p.val.2 ∈ D.carrier)))

theorem exists_full_degree_measured_vf_chain_of_smaller_ranks_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) (n+1)} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < n+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) (n+1) P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    {U V : MeasuredRVObject (M := M) (S : Set M) (n+1)} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) (n+1) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  obtain ⟨T,hT,hTB⟩ := lemma_6_29_measured hc h00 hκ.le hs hsmall (Nat.zero_lt_succ n) e
  obtain ⟨L,hL,hLB⟩ := exists_measured_vf_chain_of_component_chains
    (fun i d hd => exists_relative_measured_vf_chain_of_smaller_ranks_vfGenerated
      h00 hc hκ hs hv S B hsmall hΓ hLower d i hd) T
  exact ⟨L,hL.trans hT,fun hB => hLB (hTB hB)⟩

end DiamondIntegral.Section6
