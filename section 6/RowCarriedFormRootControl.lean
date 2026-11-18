import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».CarriedRootControl
import «section 6».RowCoordinateMeasuredObstacles

/-! (Row-form version for Remark 6.20, translated from `CarriedFormRootControl`.)
 The complete Gamma form survives every carried lower-dimensional
chain. On each output coordinate disc, all inverse points have one fixed
old context, so the old root-free-disc control applies pointwise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CarriedChainLift
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

theorem pushCoordinateRoots_form_control_row (h00 : M ⊨ Axioms.ACVF00)
    (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle)
    (ω : RowFormOn X.bundle qR)
    (hControl : CoordinateFormRootControlRow (G := G) R (rowFormExtension ω)) :
    CoordinateFormRootControlRow (G := G) (F.pushCoordinateRoots hinj R)
      (rowFormExtension (ω.comp (F.map.inverse (F.special.bijective h00)))) := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have hBij := F.special.bijective h00
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  obtain ⟨anchor,hAnchor⟩ := hBij.surjective ⟨(Fin.snoc b a,u),hCenter⟩
  have hAnchorPoint : (F.map anchor).val = (Fin.snoc b a,u) := congrArg Subtype.val hAnchor
  let oldB : Fin n → VF M := Fin.init anchor.val.1
  let oldU : Fin X.arity → RVInfinity M := anchor.val.2
  have hInput (z : VF M) (p : X.bundle) (he : (F.map p).val = (Fin.snoc b z,u)) :
      p.val = (Fin.snoc oldB z,oldU) := by
    have hInit : Fin.init (F.map p).val.1 = Fin.init (F.map anchor).val.1 := by
      rw [he,hAnchorPoint,Fin.init_snoc,Fin.init_snoc]
    have hTags : (F.map p).val.2 = (F.map anchor).val.2 := by rw [he,hAnchorPoint]
    have h := F.input_point_on_fibre hinj p anchor hInit hTags
    simpa only [he,Fin.snoc_last,oldB,oldU] using h
  have hSource (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) : (Fin.snoc oldB z,oldU) ∈ X.bundle.carrier := by
    obtain ⟨p,hp⟩ := hBij.surjective ⟨(Fin.snoc b z,u),hAmbient z hz⟩
    exact (hInput z p (congrArg Subtype.val hp)) ▸ p.property
  have hOldAvoid (z : VF M) (hz : z ∈ R.fibre oldB oldU) : z ∉ Balls.openDisc Valued.v a ρ := by
    intro hzDisc
    obtain ⟨p,hp⟩ := hBij.surjective ⟨(Fin.snoc b z,u),hAmbient z hzDisc⟩
    have hpPoint := congrArg Subtype.val hp
    have hpInput := hInput z p hpPoint
    have hpRoot : p.val ∈ R.roots.carrier := hpInput.symm ▸ ((R.mem_fibre oldB oldU z).mp hz)
    have hzNew : z ∈ (F.pushCoordinateRoots hinj R).fibre b u := by
      apply ((F.pushCoordinateRoots hinj R).mem_fibre b u z).mpr
      exact ⟨⟨p.val,hpRoot⟩,hpPoint⟩
    exact hAvoid z hzNew hzDisc
  have hValue (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
      rowFormExtension (ω.comp (F.map.inverse (F.special.bijective h00))) (Fin.snoc b z,u) =
        rowFormExtension ω (Fin.snoc oldB z,oldU) := by
    let q : F.target.bundle := ⟨(Fin.snoc b z,u),hAmbient z hz⟩
    let p := F.map.inverse hBij q
    have hp : (F.map p).val = (Fin.snoc b z,u) := congrArg Subtype.val (Map.apply_inverse F.map hBij q)
    have hpInput := hInput z p hp
    change rowFormExtension (ω.comp (F.map.inverse (F.special.bijective h00))) q.val = _
    rw [rowFormExtension_at]
    change (ω p).val = _
    have h := congrArg (rowFormExtension ω) hpInput
    rw [rowFormExtension_at] at h
    exact h
  exact (hValue x hx).trans ((hControl oldB oldU a ρ hSource hOldAvoid x hx y hy).trans (hValue y hy).symm)

end DiamondIntegral.Section6.CarriedChainLift
