import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowCarriedCoreFormCompatibility
import «section 6».CarriedApertureCompatibility
import «section 6».SimultaneousPrimitiveLifts

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleCarriedCertificates`.)
 The actual carried primitive constructions retain a simultaneous
centripetal certificate, in addition to their literal special restrictions.
The full aperture compatibility can itself be lifted at the next dimension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SimultaneousCarriedLift.identity_form_compatible_certificate_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : RowFormOn A qR) :
    let F := SimultaneousCarriedLift.identity (G := G) h00 hc hκ hs hv X P hP
    FormCompatibleSynchronizedChainRow (G := G) I X.bundle F.lift.target.bundle F.lift.map
      (fun i => rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel) (ω.comp X.oldMap) := by
  exact .identity X.bundle (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper)
    _ (fun i => X.selectedPiece_bundle_subset (P i))
    (fun i => rvCoordinateBundle_properInvariant h00 hc hκ hs hv _ X.freeLabel
      (X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i))) (ω.comp X.oldMap)

theorem SimultaneousCarriedLift.regularize_form_compatible_certificate_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : RowFormOn A qR) :
    let F := SimultaneousCarriedLift.regularize (G := G) h00 hc hκ hs hv X P hP
    FormCompatibleSynchronizedChainRow (G := G) I X.bundle F.lift.target.bundle F.lift.map
      (fun i => rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel) (ω.comp X.oldMap) := by
  let F := SimultaneousCarriedLift.regularize (G := G) h00 hc hκ hs hv X P hP
  let Q (i) := rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel
  have hBase (i) := X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i)
  have hQ (i) : ProperInvariant S (Q i).carrier := rvCoordinateBundle_properInvariant h00 hc hκ hs hv _ _ (hBase i)
  have hQD (i) : VFDoublyBounded (Q i).carrier := rvCoordinateBundle_doublyBounded _ _
    (X.selectedPiece_doublyBounded (P i)) (hBase i).rvBounded
  have hTarget : (regularizeMap X.bundle).image=F.lift.target.bundle :=
    (regularizedBundle_defSet_eq X.base X.freeLabel).symm
  exact (FormCompatibleSynchronizedChainRow.regularize X.bundle
    (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper)
    (rvCoordinateBundle_doublyBounded X.base X.freeLabel X.doublyBounded X.proper.rvBounded)
    Q (fun i => X.selectedPiece_bundle_subset (P i)) hQ hQD (ω.comp X.oldMap)).changeTarget hTarget
      (fun p => (changeMapTarget_value _ hTarget p).symm)

theorem SimultaneousCarriedLift.centripetal_form_compatible_certificate_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (E : ∀ i,CentripetalData (G := G) (P i))
    (hData : ∀ i,ApertureRestrictionData D (E i))
    (ω : RowFormOn A qR) (hSafe : D.CoreFormConstantRow ω) :
    let F := SimultaneousCarriedLift.centripetal h00 hc hκ hs hv X D P hPA E (fun i p hp => (hData i).point p hp)
    FormCompatibleSynchronizedChainRow (G := G) I X.bundle F.lift.target.bundle F.lift.map
      (fun i => rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel) (ω.comp X.oldMap) := by
  let F := SimultaneousCarriedLift.centripetal h00 hc hκ hs hv X D P hPA E (fun i p hp => (hData i).point p hp)
  let H := X.carriedComponent h00 hc hκ hs hv D
  let Q (i) := rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel
  let Y (i) := X.pieceFrame h00 hc hκ hs hv (P i) (hPA i) (E i).sourceProper
  let K (i) := (Y i).carriedComponent h00 hc hκ hs hv (E i)
  have hTarget : H.map.image=F.lift.target.bundle := defSet_eq_of_carrier_eq
    ((X.portComponent D).carryCoordinate_image X.freeLabel
      (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper))
  have hCompat (i) : ApertureRestrictionData H (K i) :=
    X.carriedComponent_restriction_data h00 hc hκ hs hv D (E i) (hPA i) (hData i)
  exact (FormCompatibleSynchronizedChainRow.centripetal X.bundle H Q
    (fun i => X.selectedPiece_bundle_subset (P i)) K hCompat (ω.comp X.oldMap)
      (X.carriedComponent_core_form_constant_row h00 hc hκ hs hv D ω hSafe)).changeTarget hTarget
      (fun p => (changeMapTarget_value _ hTarget p).symm)

end DiamondIntegral.Section6
