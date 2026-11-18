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
import «section 6».RVRefinementCoveredBases
import «section 6».RVRefinementSynchronizedChains
import «section 6».RowFormCompatibleChainTransport

/-! (Row-form version for Remark 6.20, translated from `RVRefinementGammaForms`.)
 Exact Gamma maps and semantic core constancy survive retention of
additional RV labels, with every VF coordinate unchanged by projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

namespace RVRefinementFrame

theorem gamma_form_constant_row (X : RVRefinementFrame A)
    (ω : RowFormOn A qR)
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → rowFormExtension ω p=rowFormExtension ω q) :
    ∀ p ∈ X.base.carrier,∀ q ∈ X.base.carrier,p.2=q.2 →
      rowFormExtension (ω.comp X.oldMap) p=rowFormExtension (ω.comp X.oldMap) q := by
  intro p hp q hq hTags
  have h := hConst (X.oldPoint ⟨p,hp⟩).val (X.oldPoint ⟨p,hp⟩).property
    (X.oldPoint ⟨q,hq⟩).val (X.oldPoint ⟨q,hq⟩).property (congrArg (fun u => u ∘ X.labels) hTags)
  rw [rowFormExtension_at,rowFormExtension_at] at h
  rw [rowFormExtension_at _ ⟨p,hp⟩,rowFormExtension_at _ ⟨q,hq⟩]
  exact h

theorem portComponent_core_form_constant_row (X : RVRefinementFrame A) (D : CentripetalData (G := G) A)
    (ω : RowFormOn A qR) (h : D.CoreFormConstantRow ω) :
    (X.portComponent D).CoreFormConstantRow (ω.comp X.oldMap) := by
  have hCore (p : X.base) : (X.portComponent D).core p.val=D.core (X.oldPoint p).val :=
    D.refineLabels_core X.labels X.proper X.doublyBounded
      (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres p.val p.property
  intro p q hp hq hOther hTags
  exact h (X.oldPoint p) (X.oldPoint q) ((hCore p) ▸ hp) ((hCore q) ▸ hq)
    hOther (congrArg (fun u => u ∘ X.labels) hTags)

end RVRefinementFrame

theorem RVRefinementChainLift.gamma_form_transport_row
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : RVRefinementFrame A}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : RVRefinementChainLift (G := G) X f P)
    (ω : RowFormOn A qR)
    (η : RowFormOn B qR)
    (hη : ∀ p : A,(η (f p)).val=(ω p).val) (p : X.base) :
    ((η.comp F.target.oldMap) (F.map p)).val=((ω.comp X.oldMap) p).val := by
  have he : F.target.oldPoint (F.map p)=f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val=(ω (X.oldPoint p)).val
  rw [he]
  exact hη _

end DiamondIntegral.Section6
