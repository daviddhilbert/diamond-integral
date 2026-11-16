import «section 6».RelativeAffineTailLifting
import «section 6».MeasuredVFBadLabelRepair

/-! A relatively unary change outside a positive finite head has an
actual VF unary chain, using only strictly smaller RV-rank chains for
the exceptional head labels. All coefficients are constructed over the
actual original VF-generated field base. -/

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

theorem exists_relative_tail_vf_chain_of_smaller_ranks_vfGenerated
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
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (j : Fin m) (hRelative : RVUnaryRelativeAt e.iso.hom.map (productRight (k+1) m j)) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  let d := measuredRVHeadIso hc e (productLeft (k+1) m) (productLeft (k+1) m) hU hV
  have hVol (u : U.object.domain) :
      (measuredRVHead hc V (productLeft (k+1) m) hV).object.value (d.iso.hom.map u)=
        (measuredRVHead hc U (productLeft (k+1) m) hU).object.value u := by
    funext l
    exact hRelative u (productLeft (k+1) m l) (productLeft_ne_right l j)
  let F := volumePreservingMeasuredRVLift d hVol
  obtain ⟨A,hInactive⟩ := exists_relative_fullAffineTailData_vfGenerated h00 hc hκ hs hv S B hsmall
    e hU hV F j hRelative
  obtain ⟨f,hf,hUnary,hLabels,D,hD,hDim,hGood⟩ := exists_relative_affine_lift_small_head_exception
    h00 hc hκ.le hs hsmall hΓ hv e hU hV F (fun _ => rfl) A j hInactive
  obtain ⟨T,hT,hTB⟩ := hLower (e.restrict D hD) hDim
  exact exists_repaired_relative_measured_vf_chain hc
    ((Nat.zero_lt_succ k).trans_le (Nat.le_add_right (k+1) m)) e f hf hLabels
    (productRight (k+1) m j) hUnary D hD T hT
    (fun hB => hTB ⟨U.restrict_doublyBounded _ _ hB.1,V.restrict_doublyBounded _ _ hB.2⟩) hGood

end DiamondIntegral.Section6
