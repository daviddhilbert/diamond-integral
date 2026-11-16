import «section 6».PreparedCentripetalFamilies
import «section 6».CorePartitionImages

/-! The retained-core branch of the preparation dimension induction.
An actual projected witness lifts to an actual simultaneous prepared
core witness, with the full core VF coordinate carried unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem prepared_core_of_projected_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (D : CentripetalData (G := G) A)
    (hj : D.coordinate=Fin.last n) (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (F : PreparedCentripetalFamily (G := G) D.coreProjection (fun i => (E i).coreProjection)
      (fun i => (hRestr i).core_projection_subset h00)) :
    ∃ T : PreparedCentripetalFamily (G := G) D.coreRegularizedImage (fun i => (E i).coreRegularizedImage)
        (fun i => (hRestr i).core_image_subset h00),
      ∀ p : D.coreRegularizedImage,(T.map p).val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
  exact F.carrying_coordinate h00 hc hκ hs hv
    (D.coreProjection_properInvariant h00 hc hκ hs hv) D.coreProjection_doublyBounded
    (Fin.castAdd (1+r) (Fin.last n)) D.coreRegularizedImage (fun i => (E i).coreRegularizedImage)
    (fun i => (hRestr i).core_image_subset h00) (D.coreRegularizedImage_bundle h00 hj)
    (fun i => (E i).coreRegularizedImage_bundle h00 ((hRestr i).coordinate.trans hj))

end DiamondIntegral.Section6
