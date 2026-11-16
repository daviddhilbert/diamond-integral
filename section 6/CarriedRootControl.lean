import «section 6».CarriedRootImages

/-! Coordinate-root control survives a whole carried lower-dimensional
chain, including its changing labels. Arbitrary protected source pieces
are allowed here; no cylinder condition on those pieces is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CarriedChainLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {X : CarriedRefinementFrame A}

theorem pushCoordinateRoots_control (h00 : M ⊨ Axioms.ACVF00)
    (F : CarriedChainLift (G := G) X f) (hinj : Function.Injective f)
    (R : CoordinateRootFamily X.bundle)
    (P : DefSet (rawMixedSpace (M := M) (n+1) X.arity) S) (hPX : P.carrier ⊆ X.bundle.carrier)
    (hControl : CoordinateRootControl (G := G) R P.carrier) :
    CoordinateRootControl (G := G) (F.pushCoordinateRoots hinj R) (F.map.restrict hPX).image.carrier := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have hBij := F.special.bijective h00
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  obtain ⟨anchor,hAnchor⟩ := hBij.surjective ⟨(Fin.snoc b a,u),hCenter⟩
  have hAnchorPoint : (F.map anchor).val = (Fin.snoc b a,u) := congrArg Subtype.val hAnchor
  let oldB := Fin.init anchor.val.1
  let oldU := anchor.val.2
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
  have hMembership (z : VF M) (hz : z ∈ Balls.openDisc Valued.v a ρ) :
      (Fin.snoc b z,u) ∈ (F.map.restrict hPX).image.carrier ↔ (Fin.snoc oldB z,oldU) ∈ P.carrier := by
    obtain ⟨p,hp⟩ := hBij.surjective ⟨(Fin.snoc b z,u),hAmbient z hz⟩
    have hpPoint := congrArg Subtype.val hp
    have h := restricted_image_mem_iff_of_inverse F.map hBij.injective hPX p (Fin.snoc b z,u) hpPoint
    rwa [hInput z p hpPoint] at h
  have hOld := hControl oldB oldU a ρ hSource hOldAvoid x hx y hy
  exact (hMembership x hx).trans (hOld.trans (hMembership y hy).symm)

end DiamondIntegral.Section6.CarriedChainLift
