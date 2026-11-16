import «section 6».MeasuredRVLiftRepair
import «section 6».OriginalBaseMeasuredRVLifting

/-! The full-degree lifting induction step. The existing original-base
almost-everywhere lift is repaired on a strictly lower-dimensional set
of whole old labels, using an actual lift supplied by the induction
hypothesis. Lower-dimensional head/tail constructions remain separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_everywhere_measured_rv_lift_of_smaller_label_lifts_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) (S : Set M) (n+1)} (e : MeasuredRVIso U V)
    (hLower : ∀ (D : DefSet (rawRVSpace (M := M) U.object.arity) (S : Set M))
      (hD : D.carrier ⊆ U.object.domain.carrier), rvDim D < n+1 →
        Nonempty (EverywhereMeasuredRVLift (e.restrict D hD))) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  obtain ⟨f,hf,hlab,E,hE,hDim,hGood⟩ :=
    exists_measured_rv_lift_ae_vfGenerated h00 hc hκ hs hv S B hsmall (Nat.zero_lt_succ n) e
  let D := badRVLiftLabels U.object E hE
  let hD := badRVLiftLabels_subset U.object E hE
  have hSmall : rvDim D < n+1 := badRVLiftLabels_dimension_drop hc h00 hκ.le hs hsmall hΓ hv
    U.object U.finiteVolume U.nonzero E hE hDim
  let g := Classical.choice (hLower D hD hSmall)
  exact exists_repaired_measured_rv_lift e f hf hlab E hE D hD (Set.Subset.refl _) g hGood

end DiamondIntegral.Section6
