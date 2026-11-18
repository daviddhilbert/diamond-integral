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
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowGammaCoreParameterSemantics

/-! (Row-form version for Remark 6.20, translated from `GammaCoreComponentSemantics`.)
 The first-order core test is exactly the semantic form condition
on an actual permitted centripetal component. The branch flag, old RV
labels and unchanged complementary VF coordinates are checked literally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r p : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.core_form_constant_iff_output_row
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (ω : RowFormOn A qR) :
    D.CoreFormConstantRow ω ↔
      ∀ t u : A,(D.bijection t).val.2 (Fin.castAdd r (0 : Fin 1))=branchTag true →
        (D.bijection u).val.2 (Fin.castAdd r (0 : Fin 1))=branchTag true →
        (D.bijection t).val.2=(D.bijection u).val.2 →
        (∀ i,i ≠ D.coordinate → (D.bijection t).val.1 i=(D.bijection u).val.1 i) → (ω t).val=(ω u).val := by
  constructor
  · intro h t u ht hu hTags hOther
    have htCore : D.core t.val=true := by
      apply branchTag_injective h00
      change (D.point t.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true at ht
      simpa only [CentripetalData.point,Fin.append_left] using ht
    have huCore : D.core u.val=true := by
      apply branchTag_injective h00
      change (D.point u.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true at hu
      simpa only [CentripetalData.point,Fin.append_left] using hu
    apply h t u htCore huCore
    · intro i hi
      have h := hOther i hi
      change (D.point t.val).1 i=(D.point u.val).1 i at h
      simpa only [CentripetalData.point,Function.update_of_ne hi] using h
    · funext i
      have h := congrFun hTags (Fin.natAdd 1 i)
      change (D.point t.val).2 (Fin.natAdd 1 i)=(D.point u.val).2 (Fin.natAdd 1 i) at h
      simpa only [CentripetalData.point,Fin.append_right] using h
  · intro h t u ht hu hOther hTags
    apply h t u
    · change (D.point t.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true
      simp only [CentripetalData.point,Fin.append_left,ht]
    · change (D.point u.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true
      simp only [CentripetalData.point,Fin.append_left,hu]
    · funext i
      change (D.point t.val).2 i=(D.point u.val).2 i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [CentripetalData.point,Fin.append_left,ht,hu]
      · simpa only [CentripetalData.point,Fin.append_right] using congrFun hTags j
    · intro i hi
      change (D.point t.val).1 i=(D.point u.val).1 i
      simpa only [CentripetalData.point,Function.update_of_ne hi] using hOther i hi

theorem gammaCoreConstantParameterLocus_at_component_row
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin (1+r))) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)} (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n (1+r)) D.bijection.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) :
    a ∈ gammaCoreConstantParameterLocusRow R W D.coordinate (Fin.castAdd r (0 : Fin 1)) ↔ D.CoreFormConstantRow ω := by
  rw [gammaCoreConstantParameterLocus_iff_row a R W D.bijection ω hR hW]
  exact (D.core_form_constant_iff_output_row h00 ω).symm

end DiamondIntegral.Section6
