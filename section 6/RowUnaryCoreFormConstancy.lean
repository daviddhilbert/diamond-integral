import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryFormRootControl

/-! (Row-form version for Remark 6.20, translated from `UnaryCoreFormConstancy`.)
 A small enough unary aperture makes an entire Gamma form constant
on every retained true-core label. This uses one uniform level radius,
without individual S-definable level domains or restricted components. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem CentripetalData.unary_core_congruent_row (D : CentripetalData (G := G) A) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    {p q : Mixed M 1 r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier)
    (hpCore : D.core p = true) (hqCore : D.core q = true) (hTags : p.2 = q.2) :
    Congruent (fun _ => δ) p.1 q.1 := by
  have hcoord : D.coordinate = 0 := Subsingleton.elim _ _
  have hFocus := D.extendedFocus_same_other hp hq hTags
    (fun i hi => False.elim (hi (Subsingleton.elim _ _)))
  have hpCut : vfValue (D.coefficient*D.extendedFocus p) <
      vfValue (p.1 D.coordinate-D.extendedFocus p) := of_decide_eq_true hpCore
  have hqCut : vfValue (D.coefficient*D.extendedFocus q) <
      vfValue (q.1 D.coordinate-D.extendedFocus q) := of_decide_eq_true hqCore
  have hpδ := (hCut p hp hpCore).trans_lt hpCut
  have hqδ := (hCut q hq hqCore).trans_lt hqCut
  rw [hcoord] at hpδ hqδ
  rw [← hFocus] at hqδ
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hmin := vfValue_min_le_sub (p.1 0-D.extendedFocus p) (q.1 0-D.extendedFocus p)
  rw [show (p.1 0-D.extendedFocus p)-(q.1 0-D.extendedFocus p) = p.1 0-q.1 0 by abel] at hmin
  exact (lt_min hpδ hqδ).trans_le hmin

theorem CentripetalData.unary_core_form_constant_row (D : CentripetalData (G := G) A) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → ω (a,u) = ω (b,u))
    {p q : Mixed M 1 r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier)
    (hpCore : D.core p = true) (hqCore : D.core q = true) (hTags : p.2 = q.2) : ω p = ω q := by
  have hq' : q.1 ∈ vfFibre A.carrier p.2 := by
    change (q.1,p.2) ∈ A.carrier
    rw [hTags]
    exact hq
  have h := hConst p.2 p.1 hp q.1 hq' (D.unary_core_congruent_row δ hCut hp hq hpCore hqCore hTags)
  change ω (p.1,p.2) = ω (q.1,q.2)
  rw [← hTags]
  exact h

namespace UnaryRootFamily

theorem step_same_labels_row (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (p q : A) (hTags : (stepMap D p).val.2 = (stepMap D q).val.2) :
    p.val.2 = q.val.2 ∧ D.core p.val = D.core q.val := by
  refine ⟨funext (fun i => ?_),?_⟩
  · have h := congrFun hTags (Fin.natAdd 1 (Fin.natAdd 1 i))
    simpa only [stepMap_apply,stepPoint,regularize,CentripetalData.point,Fin.append_right] using h
  · apply branchTag_injective h00
    have h := congrFun hTags (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1)))
    simpa only [stepMap_apply,stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using h

theorem step_inverse_form_constant_on_core_row
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u) = rowFormExtension ω (b,u))
    (q q' : (regularizeMap D.map.image).image)
    (hTags : q.val.2 = q'.val.2)
    (hCore : q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag true) :
    rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00))) q.val =
      rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00))) q'.val := by
  let f := stepMap D
  have hf := stepMap_bijective D h00
  let p := f.inverse hf q
  let p' := f.inverse hf q'
  have hOut : (f p).val.2 = (f p').val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hTags
  obtain ⟨hOld,hFlags⟩ := step_same_labels_row D h00 p p' hOut
  have hpCore : D.core p.val = true := by
    apply branchTag_injective h00
    have h := congrArg (fun z : (regularizeMap D.map.image).image =>
      z.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1)))) (Map.apply_inverse f hf q)
    change (stepMap D p).val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) =
      q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) at h
    have h' : branchTag (M := M) (D.core p.val) = q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) := by
      simpa only [stepMap_apply,stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using h
    exact h'.trans hCore
  have hp'Core := hFlags.symm.trans hpCore
  have hForm := D.unary_core_form_constant_row δ hCut (rowFormExtension ω) hConst
    p.property p'.property hpCore hp'Core hOld
  rw [rowFormExtension_at,rowFormExtension_at] at hForm
  rw [rowFormExtension_at,rowFormExtension_at]
  exact hForm

end UnaryRootFamily
end DiamondIntegral.Section6
