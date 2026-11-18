import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».ReleasedPullbacks

/-! (Row-form version for Remark 6.20, translated from `ReleasedGammaForms`.)
 On an actual released annulus, a form constant on the old
contracted core descends through the same coordinate projection as the
protected pieces. The form is transported through the actual new map,
with its entire graph over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def releasedGammaFormRow (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR) :
    RowFormOn (D.releasedRegularizedImage E) qR :=
  (ω.comp ((centripetalStepMap E).inverse (centripetalStepMap_bijective_row E h00))).comp
    (Map.inclusion (D.releasedRegularizedImage_subset E))

theorem releasedGammaForm_at_row (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR)
    (q : D.releasedRegularizedImage E) (p : A)
    (he : regularize (E.point p.val)=q.val) :
    rowFormExtension (D.releasedGammaFormRow E h00 ω) q.val=(ω p).val := by
  rw [rowFormExtension_at]
  change (ω ((centripetalStepMap E).inverse _
    ⟨q.val,D.releasedRegularizedImage_subset E q.property⟩)).val=(ω p).val
  have hf : centripetalStepMap E p=⟨q.val,D.releasedRegularizedImage_subset E q.property⟩ := Subtype.ext he
  rw [← hf,Map.inverse_apply]

theorem releasedGammaForm_projection_constant_row
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u)=rowFormExtension ω (b,u)) :
    ∀ q ∈ (D.releasedRegularizedImage E).carrier,∀ q' ∈ (D.releasedRegularizedImage E).carrier,
      Fin.init q.1=Fin.init q'.1 → q.2=q'.2 →
      rowFormExtension (D.releasedGammaFormRow E h00 ω) q=
        rowFormExtension (D.releasedGammaFormRow E h00 ω) q' := by
  intro q hq q' hq' hInit hTags
  obtain ⟨p,hp,hpCore,hpNew,he⟩ := (D.mem_releasedRegularizedImage E q).mp hq
  obtain ⟨p',hp',hpCore',hpNew',he'⟩ := (D.mem_releasedRegularizedImage E q').mp hq'
  let x : A := ⟨p,hp⟩
  let y : A := ⟨p',hp'⟩
  have hx : (centripetalStepMap E x).val=q := he
  have hy : (centripetalStepMap E y).val=q' := he'
  have hOldTags : p.2=p'.2 := by
    apply (E.coordinate_step_same_labels_row h00 x y ?_).1
    change (centripetalStepMap E x).val.2=(centripetalStepMap E y).val.2
    rw [hx,hy]
    exact hTags
  have hOldInit : Fin.init p.1=Fin.init p'.1 := by
    rw [← E.coordinate_step_init_row hE x,← E.coordinate_step_init_row hE y]
    rw [hx,hy]
    exact hInit
  have hForm := D.coordinate_core_form_constant_row hj δ hCut (rowFormExtension ω) hConst
    hp hp' hpCore hpCore' hOldInit hOldTags
  rw [rowFormExtension_at ω x,rowFormExtension_at ω y] at hForm
  rw [D.releasedGammaForm_at_row E h00 ω ⟨q,hq⟩ x he,D.releasedGammaForm_at_row E h00 ω ⟨q',hq'⟩ y he']
  exact hForm

theorem exists_released_gamma_descent_row
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u)=rowFormExtension ω (b,u)) :
    ∃ η : RowFormOn (D.releasedProjection E) qR,
      ∀ q : D.releasedRegularizedImage E,
        η ((vfDropLast (D.releasedRegularizedImage E)).toImage q)=D.releasedGammaFormRow E h00 ω q := by
  let h := D.releasedGammaForm_projection_constant_row E h00 hj hE δ hCut ω hConst
  exact ⟨coordinateGammaDescentRow (D.releasedGammaFormRow E h00 ω) h,
    coordinateGammaDescent_at_row (D.releasedGammaFormRow E h00 ω) h⟩

end DiamondIntegral.Section6.CentripetalData
