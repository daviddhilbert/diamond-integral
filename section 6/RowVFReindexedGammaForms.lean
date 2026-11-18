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
import «section 6».RowRVRefinementGammaForms
import «section 6».VFReindexedSynchronizedChains

/-! (Row-form version for Remark 6.20, translated from `VFReindexedGammaForms`.)
 Actual Gamma maps through VF coordinate permutations and retained
RV labels, including semantic core constancy on every ported component. -/

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

def reindexVFInverseMapRow (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n) :
    Map (reindexedVFSet A e) A :=
  (reindexVFMap (reindexedVFSet A e) e.symm).corestrict
    (fun p => (mem_reindexedVFSet A e p.val).mp p.property)

def reindexedGammaFormRow (ω : RowFormOn A qR) (e : Fin n ≃ Fin n) :
    RowFormOn (reindexedVFSet A e) qR :=
  ω.comp (reindexVFInverseMapRow A e)

theorem reindexedGammaForm_constant_row
    (ω : RowFormOn A qR) (e : Fin n ≃ Fin n)
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → rowFormExtension ω p=rowFormExtension ω q) :
    ∀ p ∈ (reindexedVFSet A e).carrier,∀ q ∈ (reindexedVFSet A e).carrier,p.2=q.2 →
      rowFormExtension (reindexedGammaFormRow ω e) p=rowFormExtension (reindexedGammaFormRow ω e) q := by
  intro p hp q hq he
  rw [rowFormExtension_at _ ⟨p,hp⟩,rowFormExtension_at _ ⟨q,hq⟩]
  have h := hConst _ (reindexVFInverseMapRow A e ⟨p,hp⟩).property
    _ (reindexVFInverseMapRow A e ⟨q,hq⟩).property he
  rw [rowFormExtension_at,rowFormExtension_at] at h
  exact h

theorem CentripetalData.reindexVF_core_form_constant_row (D : CentripetalData (G := G) A)
    (ω : RowFormOn A qR) (h : D.CoreFormConstantRow ω)
    (e : Fin n ≃ Fin n) : (D.reindexVF e).CoreFormConstantRow (reindexedGammaFormRow ω e) := by
  have hCore (p : reindexedVFSet A e) : (D.reindexVF e).core p.val=
      D.core (reindexVFInverseMapRow A e p).val := by
    have hPoint : reindexVFPoint e (reindexVFInverseMapRow A e p).val=p.val :=
      reindexVFPoint_inverse e.symm p.val
    rw [← hPoint]
    exact D.reindexVF_core e _ (reindexVFInverseMapRow A e p).property
  intro p q hp hq hOther hTags
  apply h (reindexVFInverseMapRow A e p) (reindexVFInverseMapRow A e q) ((hCore p) ▸ hp) ((hCore q) ▸ hq) _ hTags
  intro i hi
  exact hOther (e.symm i) (fun he => hi (e.symm.injective he))

def VFReindexRefinementFrame.oldMapRow {e : Fin n ≃ Fin n} (X : VFReindexRefinementFrame A e) : Map X.data.base A :=
  (reindexVFInverseMapRow A e).comp X.data.oldMap

theorem VFReindexRefinementFrame.portComponent_core_form_constant_row {e : Fin n ≃ Fin n}
    (X : VFReindexRefinementFrame A e) (D : CentripetalData (G := G) A)
    (ω : RowFormOn A qR) (h : D.CoreFormConstantRow ω) :
    (X.portComponent D).CoreFormConstantRow (ω.comp X.oldMapRow) :=
  X.data.portComponent_core_form_constant_row (D.reindexVF e) (reindexedGammaFormRow ω e) (D.reindexVF_core_form_constant_row ω h e)

theorem VFReindexRefinementFrame.gamma_form_constant_row {e : Fin n ≃ Fin n}
    (X : VFReindexRefinementFrame A e)
    (ω : RowFormOn A qR)
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → rowFormExtension ω p=rowFormExtension ω q) :
    ∀ p ∈ X.data.base.carrier,∀ q ∈ X.data.base.carrier,p.2=q.2 →
      rowFormExtension (ω.comp X.oldMapRow) p=rowFormExtension (ω.comp X.oldMapRow) q :=
  X.data.gamma_form_constant_row (reindexedGammaFormRow ω e) (reindexedGammaForm_constant_row ω e hConst)

theorem VFReindexedChainLift.gamma_form_transport_row {e : Fin n ≃ Fin n}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : VFReindexRefinementFrame A e}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : VFReindexedChainLift (G := G) X f P)
    (ω : RowFormOn A qR)
    (η : RowFormOn B qR)
    (hη : ∀ p : A,(η (f p)).val=(ω p).val) (p : X.data.base) :
    ((η.comp F.target.oldMapRow) (F.map p)).val=((ω.comp X.oldMapRow) p).val := by
  have he : F.target.oldPoint (F.map p)=f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val=(ω (X.oldPoint p)).val
  rw [he]
  exact hη _

end DiamondIntegral.Section6
