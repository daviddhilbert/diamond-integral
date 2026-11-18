import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».VariableReleaseGeometry
import «section 6».PreparedSynchronizedCarrying

/-! (Row-form version for Remark 6.20, translated from `PreparedVariableRelease`.)
 The lower-dimensional induction witness prepares the actual
variable-radius released annulus while carrying its full VF coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_variable_release_of_projected_preparation_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (D : CentripetalData (G := G) A) (hj : D.coordinate=Fin.last n)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (hStable : ∀ i,∀ a ∈ (P i).carrier, a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (ρ a.2).val < vfValue (a.1 D.coordinate-x) →
        (Function.update a.1 D.coordinate x,a.2) ∈ (P i).carrier)
    (F : PreparedSynchronizedFamily (G := G) (D.variableReleasedProjection U)
      (fun i => (E i).variableReleasedProjection U)
      (fun i => (hRestr i).variable_released_projection_subset U)) :
    ∃ T : PreparedSynchronizedFamily (G := G) (D.variableReleasedImage U)
        (fun i => (E i).variableReleasedImage U)
        (fun i => (hRestr i).variable_released_image_subset U),
      ∀ p : D.variableReleasedImage U,(T.map p).val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
  exact F.carrying_coordinate h00 hc hκ hs hv
    (D.variableReleasedProjection_properInvariant h00 hc hκ hs hv U)
    (D.variableReleasedProjection_doublyBounded U)
    (Fin.castAdd (1+r) (Fin.last n)) (D.variableReleasedImage U)
    (fun i => (E i).variableReleasedImage U)
    (fun i => (hRestr i).variable_released_image_subset U)
    (D.variableReleasedImage_bundle hj U ρ H)
    (fun i => (E i).variableReleasedImage_bundle ((hRestr i).coordinate.trans hj)
      U ρ (H.restrict (hRestr i) (hStable i)))

end DiamondIntegral.Section6
