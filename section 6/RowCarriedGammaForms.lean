import «section 6».RowCarriedFormRootControl
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowUnaryMeasuredCompatiblePreparation

/-! (Row-form version for Remark 6.20, translated from `CarriedGammaForms`.)
 Gamma forms on a prepared lower-dimensional base pull back to its
actual carried bundle. Retained labels preserve both form constancy and
the complete tuple of leading terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem CarriedRefinementFrame.bundle_tagged_row (X : CarriedRefinementFrame A)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ X.bundle.carrier, ∀ q ∈ X.bundle.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq hTags
  have hBase := labelRefinement_tagged A X.base X.labels X.fibres hTag
    (Fin.init p.1,p.2) hp.1 (Fin.init q.1,q.2) hq.1 hTags
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hp.2.trans ((congrArg (fun u => u X.freeLabel) hTags).trans hq.2.symm)
  · exact congrFun hBase j

theorem CarriedRefinementFrame.gamma_form_constant_row (X : CarriedRefinementFrame A)
    (ω : RowFormOn A qR)
    (hConst : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 →
      rowFormExtension ω p = rowFormExtension ω q) :
    ∀ p ∈ X.bundle.carrier, ∀ q ∈ X.bundle.carrier, p.2 = q.2 →
      rowFormExtension (ω.comp X.oldMap) p = rowFormExtension (ω.comp X.oldMap) q := by
  intro p hp q hq hTags
  have h := hConst (X.oldPoint ⟨p,hp⟩).val (X.oldPoint ⟨p,hp⟩).property
    (X.oldPoint ⟨q,hq⟩).val (X.oldPoint ⟨q,hq⟩).property (congrArg (fun u => u ∘ X.labels) hTags)
  rw [rowFormExtension_at,rowFormExtension_at] at h
  exact (rowFormExtension_at (ω.comp X.oldMap) (⟨p,hp⟩ : X.bundle)).trans
    (h.trans (rowFormExtension_at (ω.comp X.oldMap) (⟨q,hq⟩ : X.bundle)).symm)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : CarriedRefinementFrame A}

theorem CarriedChainLift.gamma_form_transport_row (F : CarriedChainLift (G := G) X f)
    (ω : RowFormOn A qR)
    (η : RowFormOn B qR)
    (hη : ∀ p : A, (η (f p)).val = (ω p).val) (p : X.bundle) :
    ((η.comp F.target.oldMap) (F.map p)).val = (ω (X.oldPoint p)).val := by
  have he : F.target.oldPoint (F.map p) = f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val = _
  rw [he]
  exact hη _

end DiamondIntegral.Section6
