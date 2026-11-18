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
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».SynchronizedTagComponentExtensions
import «section 6».RowFormCompatibleChainTransport

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleTagComponents`.)
 Whole-label extension preserves the actual form on each contracted
core. Inactive labels have no core, and active points recover their
literal local source and its exact Gamma value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.extendOnTags_core_form_constant_row
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (D : CentripetalData (G := G) C) (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier=(focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hTag : ∀ x ∈ A.carrier,∀ y ∈ A.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1)
    (η : RowFormOn C qR) (hSafe : D.CoreFormConstantRow η)
    (ω : RowFormOn A qR)
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,by exact ((Set.ext_iff.mp hC p.val).mp p.property).1⟩).val) :
    (D.extendOnTags U hC hA hAD hTag).CoreFormConstantRow ω := by
  let F := D.extendOnTags U hC hA hAD hTag
  intro p q hp hq hOther hTags
  have hpU : p.val.2 ∈ U.carrier := (F.core_true_active p.val hp).2
  have hqU : q.val.2 ∈ U.carrier := (F.core_true_active q.val hq).2
  have hpC : p.val ∈ C.carrier := hC.symm ▸ ⟨p.property,hpU⟩
  have hqC : q.val ∈ C.carrier := hC.symm ▸ ⟨q.property,hqU⟩
  have hCore (x : Mixed M n r) (hx : x ∈ C.carrier) : F.core x=D.core x := by
    change decide _=decide _
    rw [D.extendOnTags_extendedFocus U hC hA hAD hTag x hx]
    rfl
  have hpCore : D.core p.val=true := (hCore p.val hpC) ▸ hp
  have hqCore : D.core q.val=true := (hCore q.val hqC) ▸ hq
  exact (hForm ⟨p.val,hpC⟩).symm.trans
    ((hSafe ⟨p.val,hpC⟩ ⟨q.val,hqC⟩ hpCore hqCore hOther hTags).trans (hForm ⟨q.val,hqC⟩))

theorem exists_form_compatible_tag_component_extension_row
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (D : CentripetalData (G := G) C) (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier=(focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hTag : ∀ x ∈ A.carrier,∀ y ∈ A.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1)
    (P Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hQ : ∀ i,(Q i).carrier=(focusActive (P i) U).carrier)
    (E : ∀ i,CentripetalData (G := G) (Q i)) (hData : ∀ i,ApertureRestrictionData D (E i))
    (η : RowFormOn C qR) (hSafe : D.CoreFormConstantRow η)
    (ω : RowFormOn A qR)
    (hForm : ∀ p : C,(η p).val=(ω ⟨p.val,by exact ((Set.ext_iff.mp hC p.val).mp p.property).1⟩).val) :
    ∃ F : CentripetalData (G := G) A,∃ H : ∀ i,CentripetalData (G := G) (P i),
      F.coordinate=D.coordinate ∧ F.coefficient=D.coefficient ∧
      (∀ i,ApertureRestrictionData F (H i)) ∧
      (∀ x ∈ C.carrier,F.point x=D.point x) ∧
      (∀ x ∈ A.carrier,x.2 ∉ U.carrier → (F.point x).1=x.1) ∧
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.map.image F.bijection P ω := by
  let F := D.extendOnTags U hC hA hAD hTag
  let H (i) := (E i).extendOnTags U (hQ i) (hP i) (hAD.mono (hPA i))
    (fun x hx y hy he => hTag x (hPA i hx) y (hPA i hy) he)
  have hRestr (i) : ApertureRestrictionData F (H i) := by
    refine ⟨hPA i,(hData i).coordinate,(hData i).coefficient,?_⟩
    intro x hx
    by_cases hu : x.2 ∈ U.carrier
    · have hxC : x ∈ C.carrier := by rw [hC]; exact ⟨hPA i hx,hu⟩
      have hxQ : x ∈ (Q i).carrier := by rw [hQ i]; exact ⟨hx,hu⟩
      exact ((E i).extendOnTags_extendedFocus U (hQ i) (hP i) (hAD.mono (hPA i))
        (fun x hx y hy he => hTag x (hPA i hx) y (hPA i hy) he) x hxQ).trans
          (((hData i).focus x hxQ).trans (D.extendOnTags_extendedFocus U hC hA hAD hTag x hxC).symm)
    · have hF : x.2 ∉ F.activeTags.carrier := fun h => hu h.2
      have hH : x.2 ∉ (H i).activeTags.carrier := fun h => hu h.2
      rw [(H i).extendedFocus_inactive hH,F.extendedFocus_inactive hF]
  refine ⟨F,H,rfl,rfl,hRestr,D.extendOnTags_point U hC hA hAD hTag,?_,
    .centripetal A F P hPA H hRestr ω (D.extendOnTags_core_form_constant_row U hC hA hAD hTag η hSafe ω hForm)⟩
  intro x hx hu
  exact F.point_inactive (fun h => hu h.2)

end DiamondIntegral.Section6
