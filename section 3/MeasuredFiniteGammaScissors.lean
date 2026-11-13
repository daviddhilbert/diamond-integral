import «section 3».GammaScissors
import «section 3».MeasuredGammaProducts

/-! Finite measured Gamma objects retain arbitrary Gamma forms. Their
positive scissors use the full subcategory and the inherited restrictions. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def MeasuredFiniteGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    MeasuredFiniteGammaObject hc S k := ⟨MeasuredGammaObject.empty hc S k, fun i => i.elim0⟩

def measuredFiniteGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (MeasuredFiniteGammaObject (M := M) hc S k) where
  iso A B := Nonempty (A ≅ B)
  empty := MeasuredFiniteGammaObject.empty hc S k
  scissor A B D E := MeasuredGammaScissor A.obj B.obj D.obj E.obj

abbrev MeasuredFiniteGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (measuredFiniteGammaPresentation hc S k)

def measuredFiniteGammaClass (A : MeasuredFiniteGammaObject hc S k) : MeasuredFiniteGammaKPlus hc S k :=
  positiveClass (measuredFiniteGammaPresentation hc S k) A

def measuredFiniteGammaToGammaKPlus : MeasuredFiniteGammaKPlus hc S k →+ MeasuredGammaKPlus hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredFiniteGammaPresentation hc S k) {
    toFun A := measuredGammaClass A.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact measuredGammaClass_iso ((measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).ι.mapIso e)
    empty := measuredGammaClass_empty
    scissor := fun h => positiveClass_scissor (measuredGammaPresentation hc S k) h }

@[simp] theorem measuredFiniteGammaToGammaKPlus_class (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaToGammaKPlus (measuredFiniteGammaClass A) = measuredGammaClass A.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
