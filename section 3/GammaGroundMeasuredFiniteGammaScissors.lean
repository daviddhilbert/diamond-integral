import «section 3».GammaGroundGammaScissors
/-! Finite measured Gamma objects retain arbitrary Gamma forms. Their
positive scissors use the full subcategory and the inherited restrictions. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundMeasuredFiniteGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredFiniteGammaObject hc ground k := ⟨GammaGroundMeasuredGammaObject.empty hc ground k, fun i => i.elim0⟩

def gammaGroundMeasuredFiniteGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    ScissorPresentation (GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundMeasuredFiniteGammaObject.empty hc ground k
  scissor A B D E := GammaGroundMeasuredGammaScissor A.obj B.obj D.obj E.obj

abbrev GammaGroundMeasuredFiniteGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KPlus (gammaGroundMeasuredFiniteGammaPresentation hc ground k)

def gammaGroundMeasuredFiniteGammaClass (A : GammaGroundMeasuredFiniteGammaObject hc ground k) : GammaGroundMeasuredFiniteGammaKPlus hc ground k :=
  positiveClass (gammaGroundMeasuredFiniteGammaPresentation hc ground k) A

def gammaGroundMeasuredFiniteGammaToGammaKPlus : GammaGroundMeasuredFiniteGammaKPlus hc ground k →+ GammaGroundMeasuredGammaKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaPresentation hc ground k) {
    toFun A := gammaGroundMeasuredGammaClass A.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact gammaGroundMeasuredGammaClass_iso ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).ι.mapIso e)
    empty := gammaGroundMeasuredGammaClass_empty
    scissor := fun h => positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) h }

@[simp] theorem gammaGroundMeasuredFiniteGammaToGammaKPlus_class (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaToGammaKPlus (gammaGroundMeasuredFiniteGammaClass A) = gammaGroundMeasuredGammaClass A.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
