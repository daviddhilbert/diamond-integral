import «section 6».PaddedHeadVFChains
import «section 6».FullRankMeasuredVFChainStep

/-! The positive-codimension VF chain step. Triangular chains move
both tails into unit pads, an actual full-degree head chain is carried
with the tail fixed, and the target triangular chain is reversed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k m : ℕ}

theorem exists_finite_head_measured_vf_chain_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {d : ℕ},0 < d → ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) d} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < k+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) d P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  have hn : 0 < (k+1)+m := (Nat.zero_lt_succ k).trans_le (Nat.le_add_right (k+1) m)
  obtain ⟨A,_,hA,_,hAB⟩ := exists_padded_head_vf_chains_vfGenerated h00 hc hκ hs hv S B hsmall hΓ
    (hLower hn) U hU
  obtain ⟨_,D,_,hD,hDB⟩ := exists_padded_head_vf_chains_vfGenerated h00 hc hκ hs hv S B hsmall hΓ
    (hLower hn) V hV
  let eH := measuredRVHeadIso hc e (productLeft (k+1) m) (productLeft (k+1) m) hU hV
  obtain ⟨H,hH,hHB⟩ := exists_full_degree_measured_vf_chain_of_smaller_ranks_vfGenerated
    h00 hc hκ hs hv S B hsmall hΓ (hLower (Nat.zero_lt_succ k)) eH
  let K := H.padOnes m
  refine ⟨(A.comp K).comp D,?_,fun hB => ?_⟩
  · apply Map.ext
    intro u
    rw [MeasuredVFUnaryLiftChain.comp_map,MeasuredVFUnaryLiftChain.comp_map,hA,
      MeasuredVFUnaryLiftChain.padOnes_map,hH,hD]
    rfl
  · have hK : K.doublyBounded := H.padOnes_doublyBounded m
      (hHB ⟨measuredRVHead_doublyBounded hc U _ hU hB.1,measuredRVHead_doublyBounded hc V _ hV hB.2⟩)
    exact (A.comp K).comp_doublyBounded D (A.comp_doublyBounded K (hAB hB.1).1 hK) (hDB hB.2).2

end DiamondIntegral.Section6
