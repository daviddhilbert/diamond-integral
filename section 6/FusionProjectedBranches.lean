import «section 6».FusionActualStages
import «section 6».ArbitraryCoordinateBranches

/-! The actual lower-dimensional induction witness prepares both
replacement branches of a fusion step, including every protected set
and whichever VF coordinate is active. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def SynchronizedPreparationInDimension (S : Set M) (n k : ℕ) : Prop :=
  ∀ r,(H : DefSet (rawMixedSpace (M := M) n r) S) →
    ProperInvariant S H.carrier → VFDoublyBounded H.carrier → IsRVPullback H.carrier →
    ∀ P : Fin k → DefSet (rawMixedSpace (M := M) n r) S,
    ∀ hPH : ∀ i,(P i).carrier ⊆ H.carrier,(∀ i,ProperInvariant S (P i).carrier) →
      Nonempty (PreparedSynchronizedFamily (G := G) H P hPH)

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
namespace CentripetalFusionRepair
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

theorem prepared_core_of_dimension_induction
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k) :
    Nonempty (PreparedSynchronizedFamily (G := G) R.component.coreRegularizedImage
      (fun i => (R.protectedComponent i).coreRegularizedImage)
      (fun i => (R.protectedComponent_compatible i).core_image_subset h00)) := by
  let e := Equiv.swap (Fin.last n) R.component.coordinate
  have he : e (Fin.last n)=R.component.coordinate := Equiv.swap_apply_left _ _
  have hRP := R.component.coreRegularizedImage_rvPullback h00 R.context.pullback
  obtain ⟨F⟩ := hIH _ (coordinateProjection R.component.coreRegularizedImage e)
    (coordinateProjection_properInvariant _ e (R.component.coreRegularizedImage_properInvariant h00 hc hκ hs hv))
    (coordinateProjection_doublyBounded _ e R.component.coreRegularizedImage_doublyBounded)
    (vfDropLast_image_rvPullback (reindexedVFSet_rvPullback _ e hRP))
    (fun i => coordinateProjection (R.protectedComponent i).coreRegularizedImage e)
    (fun i => coordinateProjection_subset ((R.protectedComponent_compatible i).core_image_subset h00) e)
    (fun i => coordinateProjection_properInvariant _ e
      ((R.protectedComponent i).coreRegularizedImage_properInvariant h00 hc hκ hs hv))
  exact synchronized_core_in_arbitrary_coordinate h00 hc hκ hs hv R.component R.sourcePiece
    R.protectedComponent R.protectedComponent_compatible e he F

theorem prepared_release_of_dimension_induction
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    Nonempty (PreparedSynchronizedFamily (G := G) (R.component.variableReleasedImage (R.releaseTags hCoeffMem))
      (fun i => (R.protectedComponent i).variableReleasedImage (R.releaseTags hCoeffMem))
      (fun i => (R.protectedComponent_compatible i).variable_released_image_subset (R.releaseTags hCoeffMem))) := by
  let U := R.releaseTags hCoeffMem
  let e := Equiv.swap (Fin.last n) R.component.coordinate
  have he : e (Fin.last n)=R.component.coordinate := Equiv.swap_apply_left _ _
  have hRP : IsRVPullback (R.component.variableReleasedImage U).carrier :=
    focusActive_rvPullback _ U (R.stageTarget_rvPullback h00)
  obtain ⟨F⟩ := hIH _ (coordinateProjection (R.component.variableReleasedImage U) e)
    (coordinateProjection_properInvariant _ e (R.component.variableReleasedImage_properInvariant h00 hc hκ hs hv U))
    (coordinateProjection_doublyBounded _ e (R.component.variableReleasedImage_doublyBounded U))
    (vfDropLast_image_rvPullback (reindexedVFSet_rvPullback _ e hRP))
    (fun i => coordinateProjection ((R.protectedComponent i).variableReleasedImage U) e)
    (fun i => coordinateProjection_subset ((R.protectedComponent_compatible i).variable_released_image_subset U) e)
    (fun i => coordinateProjection_properInvariant _ e
      ((R.protectedComponent i).variableReleasedImage_properInvariant h00 hc hκ hs hv U))
  exact synchronized_variable_release_in_arbitrary_coordinate h00 hc hκ hs hv R.component U R.oldRadius
    (R.old_aperture_release_data h00 hCoeffMem) R.sourcePiece R.protectedComponent R.protectedComponent_compatible
    (R.old_aperture_protected_stable hCoeffMem) e he F

end CentripetalFusionRepair
end DiamondIntegral.Section6
