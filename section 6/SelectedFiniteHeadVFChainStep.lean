import «section 6».FiniteHeadMeasuredVFChainStep
import «section 6».MeasuredVFPermutations
import «section 6».MeasuredRVReindexingTransfer
import Section9.FiniteHeadCover

/-! Selected source and target finite heads give actual VF unary chains
in the original coordinates. The coordinate changes, triangular padding
and every intermediate double bound are fully constructed. -/

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

theorem exists_selected_finite_head_vf_chain_vfGenerated
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
    (v w : Fin (k+1) ↪ Fin ((k+1)+m))
    (hU : (rvHeadVolume U.object v).FiniteFibres) (hV : (rvHeadVolume V.object w).FiniteFibres) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  obtain ⟨a,ha⟩ := exists_head_reindex v
  obtain ⟨b,hb⟩ := exists_head_reindex w
  let l := productLeft (k+1) m
  let UR := U.reindexVolume a
  let VR := V.reindexVolume b
  let eR := measuredRVReindexedIso e a b
  have hUR : (rvHeadVolume UR.object l).FiniteFibres := by
    have he : rvHeadVolume UR.object l = rvHeadVolume U.object v := by
      apply Map.ext
      intro u
      apply Subtype.ext
      funext i
      exact congrArg (U.object.value u) (ha i)
    rw [he]
    exact hU
  have hVR : (rvHeadVolume VR.object l).FiniteFibres := by
    have he : rvHeadVolume VR.object l = rvHeadVolume V.object w := by
      apply Map.ext
      intro u
      apply Subtype.ext
      funext i
      exact congrArg (V.object.value u) (hb i)
    rw [he]
    exact hV
  obtain ⟨T,hT,hTB⟩ := exists_finite_head_measured_vf_chain_vfGenerated h00 hc hκ hs hv S B hsmall hΓ
    hLower eR hUR hVR
  have hn : 0 < (k+1)+m := (Nat.zero_lt_succ k).trans_le (Nat.le_add_right (k+1) m)
  obtain ⟨A,hA,hAB⟩ := exists_measured_vf_permutation_chain hc hn U a
  obtain ⟨D,hD,hDB⟩ := exists_measured_vf_inverse_permutation_chain hc hn V b
  refine ⟨(A.comp T).comp D,?_,fun hB => ?_⟩
  · apply Map.ext
    intro u
    rw [MeasuredVFUnaryLiftChain.comp_map,MeasuredVFUnaryLiftChain.comp_map,hA,hT,hD]
    rfl
  · have hURB := rvReindexVolume_doublyBounded U.object a hB.1
    have hVRB := rvReindexVolume_doublyBounded V.object b hB.2
    exact (A.comp T).comp_doublyBounded D (A.comp_doublyBounded T (hAB hB.1) (hTB ⟨hURB,hVRB⟩)) (hDB hB.2)

end DiamondIntegral.Section6
