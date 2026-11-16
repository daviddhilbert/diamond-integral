import «section 6».MeasuredRVTailReplacements
import «section 6».RelativeTailVFChainStep

/-! Fuse actual triangular tail changes into a whole-domain measured
VF unary chain whenever a positive finite coordinate head has the same
source and target values. Every intermediate bound is retained. -/

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

theorem exists_tail_measured_vf_chain_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < k+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hHead : ∀ u l,V.object.value (e.iso.hom.map u) (productLeft (k+1) m l)=U.object.value u (productLeft (k+1) m l)) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  let P (J : Finset (Fin m)) := measuredRVTailReplacement hc e hU J
  have hPB (J : Finset (Fin m)) (hB : U.doublyBounded ∧ V.doublyBounded) : (P J).doublyBounded :=
    measuredRVTailReplacement_doublyBounded hc e hU J hB.1 hB.2
  have hPart (J : Finset (Fin m)) :
      ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) (P ∅) (P J),
        (∀ u,T.iso.iso.hom.map u=u) ∧ ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
    induction J using Finset.induction_on with
    | empty => exact ⟨.identity _,fun _ => rfl,hPB ∅⟩
    | @insert j J hj ih =>
      obtain ⟨T,hT,hTB⟩ := ih
      let d := measuredRVTailReplacementStep hc e hU J j
      obtain ⟨K,hK,hKB⟩ := exists_relative_tail_vf_chain_of_smaller_ranks_vfGenerated h00 hc hκ hs hv
        S B hsmall hΓ hLower d (measuredRVTailReplacement_headFinite hc e hU J)
        (measuredRVTailReplacement_headFinite hc e hU (insert j J)) j
        (measuredRVTailReplacementStep_unary hc e hU J j)
      refine ⟨T.comp K,fun u => ?_,fun hB => T.comp_doublyBounded K (hTB hB) (hKB ⟨hPB J hB,hPB (insert j J) hB⟩)⟩
      rw [MeasuredVFUnaryLiftChain.comp_map,hT,hK]
      rfl
  obtain ⟨T,hT,hTB⟩ := hPart Finset.univ
  have hSource (u : U.object.domain) : (P ∅).object.value u=U.object.value u := by
    apply productTuple_ext
    · exact fun l => measuredRVTailReplacement_head hc e hU ∅ u l
    · intro j
      rw [measuredRVTailReplacement_tail]
      simp only [Finset.notMem_empty,if_false]
  have hTarget (u : U.object.domain) : V.object.value (e.iso.hom.map u)=(P Finset.univ).object.value u := by
    apply productTuple_ext
    · intro l
      rw [measuredRVTailReplacement_head]
      exact hHead u l
    · intro j
      rw [measuredRVTailReplacement_tail]
      simp only [Finset.mem_univ,if_true]
  let a : MeasuredRVIso U (P ∅) := {
    iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id hSource
    balance u := (measuredRVTailReplacement_totalWeight hc e hU ∅ u).symm }
  let b : MeasuredRVIso (P Finset.univ) V := {
    iso := rvIsoOfVolumePreservingBijection e.iso.hom.map (rvIso_map_bijective e.iso) hTarget
    balance u := (measuredRVTailReplacement_totalWeight hc e hU Finset.univ u).trans (e.balance u) }
  let A := volumePreservingMeasuredRVLift a hSource
  let B₁ := volumePreservingMeasuredRVLift b hTarget
  let i : Fin ((k+1)+m) := ⟨0,(Nat.zero_lt_succ k).trans_le (Nat.le_add_right (k+1) m)⟩
  let L : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U (P Finset.univ) :=
    .step i A (volumePreservingMeasuredRVLift_unary a hSource i) T
  let H : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) (P Finset.univ) V :=
    .step i B₁ (volumePreservingMeasuredRVLift_unary b hTarget i) (.identity V)
  refine ⟨L.comp H,?_,fun hB => L.comp_doublyBounded H ⟨hB.1,hTB hB⟩ ⟨hPB Finset.univ hB,hB.2⟩⟩
  apply Map.ext
  intro u
  rw [MeasuredVFUnaryLiftChain.comp_map]
  change e.iso.hom.map (T.iso.iso.hom.map u)=e.iso.hom.map u
  rw [hT]

end DiamondIntegral.Section6
