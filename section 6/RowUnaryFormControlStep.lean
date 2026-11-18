import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryCoreFormConstancy

/-! (Row-form version for Remark 6.20, translated from `UnaryFormControlStep`.)
 Root-free-disc control of an entire Gamma form survives an actual
unary root step. The noncore inverse is the old translation; all true
core labels have constant transported form by the common level radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryRootFamily
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem noncore_transported_form_value_row
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR)
    (q : (regularizeMap D.map.image).image)
    (hFlag : q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00))) q.val =
      rowFormExtension ω ((fun _ : Fin 1 => q.val.1 0+D.unaryTagFocus (oldTags q.val.2)),oldTags q.val.2) := by
  obtain ⟨p,he,hTags,hCore,hScalar⟩ := noncore_input D h00 q.val q.property hFlag
  have hpq : stepMap D p = q := Subtype.ext he
  have hInverse : (stepMap D).inverse (stepMap_bijective D h00) q = p := by
    rw [← hpq,Map.inverse_apply]
  have hPoint : p.val = ((fun _ : Fin 1 => q.val.1 0+D.unaryTagFocus (oldTags q.val.2)),oldTags q.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      exact hScalar
    · exact hTags
  rw [rowFormExtension_at]
  change (ω ((stepMap D).inverse (stepMap_bijective D h00) q)).val = _
  rw [hInverse,← hPoint,rowFormExtension_at]

theorem noncore_form_root_control_step_row
    (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (ω : RowFormOn A qR)
    (hControl : UnaryFormRootControlRow (G := G) R (rowFormExtension ω))
    (u : Fin (1+(1+r)) → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G)
    (hFlag : u (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false)
    (hAmbient : ∀ x ∈ Balls.openDisc Valued.v a ρ,
      ((fun _ : Fin 1 => x),u) ∈ (regularizeMap D.map.image).image.carrier)
    (hAvoid : ∀ x ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u, x ∉ Balls.openDisc Valued.v a ρ)
    (x : VF M) (hx : x ∈ Balls.openDisc Valued.v a ρ) (y : VF M) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00))) ((fun _ : Fin 1 => x),u) =
      rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00))) ((fun _ : Fin 1 => y),u) := by
  let v := oldTags u
  let focusVal := D.unaryTagFocus v
  have hShift (z : VF M) :
      z ∈ Balls.openDisc Valued.v (a+focusVal) ρ ↔ z-focusVal ∈ Balls.openDisc Valued.v a ρ := by
    simpa only [add_sub_cancel_right] using (Balls.sub_mem_openDisc_iff Valued.v (a+focusVal) focusVal z ρ).symm
  have hSource (z : VF M) (hz : z ∈ Balls.openDisc Valued.v (a+focusVal) ρ) :
      ((fun _ : Fin 1 => z),v) ∈ A.carrier := by
    have hm := noncore_inverse_mem D h00 (hAmbient (z-focusVal) ((hShift z).mp hz)) hFlag
    simpa only [v,focusVal,sub_add_cancel] using hm
  have hOldAvoid (z : VF M) (hz : z ∈ R.fibre v) : z ∉ Balls.openDisc Valued.v (a+focusVal) ρ := by
    intro hzDisc
    have hq := hAmbient (z-focusVal) ((hShift z).mp hzDisc)
    obtain ⟨p,he,hu,hCore,hScalar⟩ := noncore_input D h00 _ hq hFlag
    have hScalar' : p.val.1 0 = z := by simpa only [v,focusVal,sub_add_cancel] using hScalar
    have hpRoot : p.val ∈ R.roots.carrier := by
      have hpEq : p.val = ((fun _ : Fin 1 => z),v) := by
        apply Prod.ext
        · funext i; fin_cases i; exact hScalar'
        · exact hu
      rw [hpEq]
      exact (R.mem_fibre v z).mp hz
    have hChild : z-focusVal ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u := by
      apply ((R.stepFamily D h00 hcoord hact hfocus).mem_fibre u _).mpr
      exact (R.remainingRoots_iff D h00 _).mpr ⟨p,hpRoot,hCore,he⟩
    exact hAvoid (z-focusVal) hChild ((hShift z).mp hzDisc)
  have hxOld : x+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hx)
  have hyOld : y+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hy)
  have hOld := hControl v (a+focusVal) ρ hSource hOldAvoid (x+focusVal) hxOld (y+focusVal) hyOld
  exact (noncore_transported_form_value_row D h00 ω ⟨_,hAmbient x hx⟩ hFlag).trans
    (hOld.trans (noncore_transported_form_value_row D h00 ω ⟨_,hAmbient y hy⟩ hFlag).symm)

theorem form_root_control_step_row
    (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u) = rowFormExtension ω (b,u))
    (hControl : UnaryFormRootControlRow (G := G) R (rowFormExtension ω)) :
    UnaryFormRootControlRow (G := G) (R.stepFamily D h00 hcoord hact hfocus)
      (rowFormExtension (ω.comp ((stepMap D).inverse (stepMap_bijective D h00)))) := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  rcases step_image_branch D h00 hCenter with hFalse | hTrue
  · exact noncore_form_root_control_step_row R D h00 hcoord hact hfocus ω hControl u a ρ hFalse hAmbient hAvoid x hx y hy
  · exact step_inverse_form_constant_on_core_row D h00 δ hCut ω hConst
      ⟨_,hAmbient x hx⟩ ⟨_,hAmbient y hy⟩ rfl hTrue

end DiamondIntegral.Section6.UnaryRootFamily
