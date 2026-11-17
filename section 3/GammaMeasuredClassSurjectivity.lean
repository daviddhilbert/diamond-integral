import «section 3».GammaMeasuredClassLift
import «section 3».GammaMeasuredObjectSurjectivity

/-! Surjectivity of the actual Gamma-valued forward lift on each
positive additive scissor monoid. No kernel input is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3

theorem positiveAdditiveHom_surjective_of_classes {Obj R : Type*} [AddCommMonoid R]
    (P : PositiveAdditiveGrothendieck.Presentation Obj)
    (F : R →+ PositiveAdditiveGrothendieck.KPlus P)
    (h : ∀ A, ∃ x, F x = PositiveAdditiveGrothendieck.of P A) : Function.Surjective F := by
  intro z
  obtain ⟨p,rfl⟩ := (PositiveAdditiveGrothendieck.congruence P).mk'_surjective z
  let Q := PositiveAdditiveGrothendieck.quotientHom P
  change ∃ x,F x = Q p
  induction p using Finsupp.induction_linear with
  | zero => exact ⟨0,(map_zero F).trans (map_zero Q).symm⟩
  | add p q hp hq =>
    obtain ⟨x,hx⟩ := hp
    obtain ⟨y,hy⟩ := hq
    exact ⟨x+y,(map_add F x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add Q p q).symm)⟩
  | single A b =>
    obtain ⟨x,hx⟩ := h A
    have hsingle : Finsupp.single A b = b • PositiveAdditiveGrothendieck.generator A := by
      induction b with
      | zero => simp only [Finsupp.single_zero,zero_nsmul]
      | succ b ih =>
        rw [Finsupp.single_add,ih,add_nsmul,one_nsmul]
        rfl
    refine ⟨b • x,?_⟩
    rw [hsingle,map_nsmul,map_nsmul,hx]
    rfl

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasuredRVClassLift_surjective
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hB : GammaParameters.VFGammaGeneratedBase B)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (n : ℕ) :
    Function.Surjective (gammaMeasuredRVClassLift (hc := hc) (k := n) hκ.le hs h00 hr hB hv) := by
  apply positiveAdditiveHom_surjective_of_classes
    (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) hκ.le hs hr hv n)
  intro U
  obtain ⟨W,hW⟩ := gammaMeasuredVFObject_class_preimage hκ hs h00 hr hv U
  exact ⟨gammaGroundMeasuredRVClass W,(gammaMeasuredRVClassLift_class hκ.le hs h00 hr hB hv W).trans hW.symm⟩

end DiamondIntegral.Section3
