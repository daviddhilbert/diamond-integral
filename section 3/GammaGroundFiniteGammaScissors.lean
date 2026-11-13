import «section 3».GammaGroundGammaScissors
/-! Actual finite Gamma scissors and the forgetful positive map to
the complete Gamma-ground category. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundFiniteGammaObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    GammaGroundFiniteGammaObject hc ground k := ⟨GammaGroundGammaObject.empty hc ground k, fun i => i.elim0⟩

def GammaGroundFiniteGammaObject.restrict (A : GammaGroundFiniteGammaObject hc ground k)
    (X : Fin A.obj.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)))
    (hX : ∀ i, (X i).carrier ⊆ (A.obj.piece i).carrier) : GammaGroundFiniteGammaObject hc ground k :=
  ⟨A.obj.restrict X, fun i => (A.property i).subset (hX i)⟩

def gammaGroundFiniteGammaPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    ScissorPresentation (GammaGroundFiniteGammaObject (M := M) hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundFiniteGammaObject.empty hc ground k
  scissor A B D E := GammaGroundGammaScissor A.obj B.obj D.obj E.obj

abbrev GammaGroundFiniteGammaKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  KPlus (gammaGroundFiniteGammaPresentation hc ground k)

def gammaGroundFiniteGammaClass (A : GammaGroundFiniteGammaObject hc ground k) : GammaGroundFiniteGammaKPlus hc ground k :=
  positiveClass (gammaGroundFiniteGammaPresentation hc ground k) A

def gammaGroundFiniteGammaToGammaKPlus : GammaGroundFiniteGammaKPlus hc ground k →+ GammaGroundGammaKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundFiniteGammaPresentation hc ground k) {
    toFun A := gammaGroundGammaClass A.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact gammaGroundGammaClass_iso ((gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).ι.mapIso e)
    empty := gammaGroundGammaClass_empty
    scissor := fun h => positiveClass_scissor (gammaGroundGammaPresentation hc ground k) h }

@[simp] theorem gammaGroundFiniteGammaToGammaKPlus_class (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaToGammaKPlus (gammaGroundFiniteGammaClass A) = gammaGroundGammaClass A.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ A


end DiamondIntegral.Section3
