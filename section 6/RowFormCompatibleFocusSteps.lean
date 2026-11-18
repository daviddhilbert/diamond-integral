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
import «section 6».RowFormCompatibleSynchronizedChains

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleFocusSteps`.)
 A common permitted centripetal step with core-form constancy,
followed by actual regularization, retains the measured component
invariant. The intermediate Gamma form is the actual inverse transportRow. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem form_compatible_centripetal_step_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (ω : RowFormOn A qR) (hForm : D.CoreFormConstantRow ω) :
    FormCompatibleSynchronizedChainRow (G := G) I A (regularizeMap D.map.image).image (centripetalStepMap D) P ω := by
  let hPA (i) := (hRestr i).subset
  let Q (i) := (D.bijection.restrict (hPA i)).image
  have hQsub (i) : (Q i).carrier ⊆ D.map.image.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (D.bijection ⟨p.val,hPA i p.property⟩).property
  have hQeq (i) : (E i).map.image=Q i :=
    image_eq_of_surjective_liesOver D.bijection (E i).bijection ((E i).bijective h00).surjective
      (hPA i) (fun p => (hRestr i).point p.val p.property)
  have hQ (i) : ProperInvariant S (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_properInvariant h00 hc hκ hs hv
  have hQD (i) : VFDoublyBounded (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_vfDoublyBounded
  let η := ω.comp (D.bijection.inverse (D.bijective h00))
  have hTransport (p : A) : (η (D.bijection p)).val=(ω p).val := by
    change (ω (D.bijection.inverse _ (D.bijection p))).val=(ω p).val
    rw [Map.inverse_apply]
  exact .comp P hPA (.centripetal A D P hPA E hRestr ω hForm) η hTransport
    (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
      Q hQsub hQ hQD η)

end DiamondIntegral.Section6
