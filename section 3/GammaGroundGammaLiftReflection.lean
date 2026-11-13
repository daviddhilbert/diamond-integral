import «section 3».GammaGroundRVFamilyReflection
import «section 3».GammaGroundGammaRVLift
import «section 3».GammaGroundGammaCodeDescent
import «section 3».GammaGroundRVIsomorphismClasses
import «section 3».GammaGroundGammaRVScissors
import «section 3».GammaGroundGammaRepresentatives
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundGammaCodeBijectionOfLift {A D : GammaGroundGammaObject hc B k}
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain) :
    GammaGroundFamilyBijection A.codeLift D.codeLift :=
  D.rvCodeBijection.symm.comp
    ((gammaGroundRVFamilyBijectionOfRealization F).comp A.rvCodeBijection)

/-- The exact extra condition needed for a particular lifted bijection
to descend is preservation and reflection of the full value equivalence. -/
def gammaGroundGammaHomOfLiftBijection {A D : GammaGroundGammaObject hc B k}
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain)
    (hF : ∀ c d, A.decode c = A.decode d ↔
      D.decode ((gammaGroundGammaCodeBijectionOfLift F).equiv c) =
        D.decode ((gammaGroundGammaCodeBijectionOfLift F).equiv d)) : A ⟶ D :=
  GammaGroundGammaHom.ofCodeBijection (gammaGroundGammaCodeBijectionOfLift F) hF

/-- For singleton Gamma domains the value relation is constant. Thus any
actual same-ground RV lift bijection already supplies the contraction,
including at values without a definable RV representative. -/
def gammaGroundGammaSubsingletonHomOfLift {A D : GammaGroundGammaObject hc B k}
    [Subsingleton A.Carrier] [Subsingleton D.Carrier]
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain) : A ⟶ D := by
  apply gammaGroundGammaHomOfLiftBijection F
  intro c d
  exact ⟨fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩

theorem gammaGroundGammaZero_decode_injective (A : GammaGroundGammaObject hc B 0) :
    Function.Injective A.decode := by
  rintro ⟨i,c⟩ ⟨j,d⟩ he
  have hij : i = j := congrArg Sigma.fst he
  subst j
  apply congrArg (Sigma.mk i)
  apply Subtype.ext
  apply Subtype.ext
  funext u
  exact u.1.elim0

/-- In degree zero decoding has singleton fibres, so every actual RV
bijection between lifts descends to a Gamma isomorphism. -/
def gammaGroundGammaZeroHomOfLift {A D : GammaGroundGammaObject hc B 0}
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain) : A ⟶ D := by
  apply gammaGroundGammaHomOfLiftBijection F
  intro c d
  constructor
  · intro h
    exact congrArg (fun c => D.decode ((gammaGroundGammaCodeBijectionOfLift F).equiv c))
      (gammaGroundGammaZero_decode_injective A h)
  · intro h
    apply congrArg A.decode
    exact (gammaGroundGammaCodeBijectionOfLift F).equiv.injective
      (gammaGroundGammaZero_decode_injective D h)

theorem gammaGroundGammaToRVKPlus_zero_injective :
    Function.Injective (gammaGroundGammaToRVKPlus (hc := hc) (ground := B) (k := 0)) := by
  intro x y h
  obtain ⟨A,rfl⟩ := gammaGroundGammaClass_surjective x
  obtain ⟨D,rfl⟩ := gammaGroundGammaClass_surjective y
  simp only [gammaGroundGammaToRVKPlus_class] at h
  obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp h
  exact gammaGroundGammaClass_iso (asIso (gammaGroundGammaZeroHomOfLift e.hom))
end DiamondIntegral.Section3
