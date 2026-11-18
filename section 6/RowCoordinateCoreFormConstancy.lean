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
import «section 6».RowBinaryMeasuredRootTermination

/-! (Row-form version for Remark 6.20, translated from `CoordinateCoreFormConstancy`.)
 A common aperture radius controls the complete Gamma form on a
last-coordinate core. The complementary VF tuple and old RV labels
are checked explicitly; no individual level is assumed definable. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem centripetalStepMap_bijective_row (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective (centripetalStepMap D) := (regularization_bijective _).comp (D.bijective h00)

theorem CentripetalData.coordinate_step_init_row (D : CentripetalData (G := G) A)
    (hj : D.coordinate = Fin.last n) (p : A) :
    Fin.init ((centripetalStepMap D) p).val.1 = Fin.init p.val.1 := by
  change Fin.init (D.point p.val).1 = Fin.init p.val.1
  funext i
  simp only [CentripetalData.point,hj,Fin.init,Function.update_of_ne (Fin.castSucc_ne_last i)]

theorem CentripetalData.coordinate_step_same_labels_row (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (p q : A)
    (hTags : ((centripetalStepMap D) p).val.2 = ((centripetalStepMap D) q).val.2) :
    p.val.2 = q.val.2 ∧ D.core p.val = D.core q.val := by
  change (regularize (D.point p.val)).2 = (regularize (D.point q.val)).2 at hTags
  refine ⟨funext (fun i => ?_),?_⟩
  · have h := congrFun hTags (Fin.natAdd (n+1) (Fin.natAdd 1 i))
    simpa only [regularize,CentripetalData.point,Fin.append_right] using h
  · apply branchTag_injective h00
    have h := congrFun hTags (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))
    simpa only [regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using h

theorem CentripetalData.coordinate_core_congruent_row (D : CentripetalData (G := G) A)
    (hj : D.coordinate = Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    {p q : Mixed M (n+1) r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier)
    (hpCore : D.core p = true) (hqCore : D.core q = true)
    (hInit : Fin.init p.1 = Fin.init q.1) (hTags : p.2 = q.2) :
    Congruent (fun _ => δ) p.1 q.1 := by
  have hOther (i : Fin (n+1)) (hi : i ≠ D.coordinate) : p.1 i = q.1 i := by
    rw [hj] at hi
    exact Fin.lastCases (motive := fun j => j ≠ Fin.last n → p.1 j = q.1 j)
      (fun hn => False.elim (hn rfl)) (fun j _ => congrFun hInit j) i hi
  have hFocus := D.extendedFocus_same_other hp hq hTags hOther
  have hpCut : vfValue (D.coefficient*D.extendedFocus p) <
      vfValue (p.1 D.coordinate-D.extendedFocus p) := of_decide_eq_true hpCore
  have hqCut : vfValue (D.coefficient*D.extendedFocus q) <
      vfValue (q.1 D.coordinate-D.extendedFocus q) := of_decide_eq_true hqCore
  have hpδ := (hCut p hp hpCore).trans_lt hpCut
  have hqδ := (hCut q hq hqCore).trans_lt hqCut
  rw [hj] at hpδ hqδ
  rw [← hFocus] at hqδ
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hmin := vfValue_min_le_sub (p.1 (Fin.last n)-D.extendedFocus p) (q.1 (Fin.last n)-D.extendedFocus p)
    rw [show (p.1 (Fin.last n)-D.extendedFocus p)-(q.1 (Fin.last n)-D.extendedFocus p) =
      p.1 (Fin.last n)-q.1 (Fin.last n) by abel] at hmin
    exact (lt_min hpδ hqδ).trans_le hmin
  · have he : p.1 j.castSucc = q.1 j.castSucc := congrFun hInit j
    simpa only [he] using (Congruent.refl (fun _ => δ) q.1 j.castSucc)

theorem CentripetalData.coordinate_core_form_constant_row (D : CentripetalData (G := G) A)
    (hj : D.coordinate = Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Mixed M (n+1) r → Set (rawRVSpace (M := M) qR).Carrier)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → ω (a,u) = ω (b,u))
    {p q : Mixed M (n+1) r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier)
    (hpCore : D.core p = true) (hqCore : D.core q = true)
    (hInit : Fin.init p.1 = Fin.init q.1) (hTags : p.2 = q.2) : ω p = ω q := by
  have hq' : q.1 ∈ vfFibre A.carrier p.2 := by
    change (q.1,p.2) ∈ A.carrier
    rw [hTags]
    exact hq
  have h := hConst p.2 p.1 hp q.1 hq' (D.coordinate_core_congruent_row hj δ hCut hp hq hpCore hqCore hInit hTags)
  change ω (p.1,p.2) = ω (q.1,q.2)
  rw [← hTags]
  exact h

theorem CentripetalData.coordinate_step_inverse_form_constant_on_core_row
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate = Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u) = rowFormExtension ω (b,u))
    (q q' : (regularizeMap D.map.image).image)
    (hInit : Fin.init q.val.1 = Fin.init q'.val.1) (hTags : q.val.2 = q'.val.2)
    (hCore : q.val.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag true) :
    rowFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective_row D h00))) q.val =
      rowFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective_row D h00))) q'.val := by
  let f := centripetalStepMap D
  have hf := centripetalStepMap_bijective_row D h00
  let p := f.inverse hf q
  let p' := f.inverse hf q'
  have hOut : (f p).val.2 = (f p').val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hTags
  obtain ⟨hOld,hFlags⟩ := D.coordinate_step_same_labels_row h00 p p' hOut
  have hOldInit : Fin.init p.val.1 = Fin.init p'.val.1 := by
    rw [← D.coordinate_step_init_row hj p,← D.coordinate_step_init_row hj p']
    change Fin.init (f p).val.1 = Fin.init (f p').val.1
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hInit
  have hpCore : D.core p.val = true := by
    apply branchTag_injective h00
    have h := congrArg (fun z : (regularizeMap D.map.image).image =>
      z.val.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))) (Map.apply_inverse f hf q)
    change (regularize (D.point p.val)).2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = _ at h
    rw [D.regularized_core_flag] at h
    exact h.trans hCore
  have hForm := D.coordinate_core_form_constant_row hj δ hCut (rowFormExtension ω) hConst
    p.property p'.property hpCore (hFlags.symm.trans hpCore) hOldInit hOld
  rw [rowFormExtension_at,rowFormExtension_at] at hForm
  rw [rowFormExtension_at,rowFormExtension_at]
  exact hForm

end DiamondIntegral.Section6
