import «section 3».GammaGroundContext
import «section 3».GammaGroundVFSemiring
import «section 3».GammaGroundRVGenerators
import «section 3».GammaGroundLifting
import «section 3».CompletionEquivalences
import «section 3».PresentationHomExt

/-! Replaceable input from accepted source [18], Proposition 6.18 and
Theorem 6.19, over actual Gamma ground parameters. The full model, genuine
real VF generation, smallness and nontrivial Gamma hypotheses are retained.
The results below concern the concrete universal presentations; their
comparison with the manuscript's grading and filtration is separate. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundObjectLiftFinite {k : ℕ} (U : GammaGroundRVObject hc ground k) : GammaGroundFiniteVFObject hc ground :=
  ⟨k, U.arity, gammaGroundObjectLift U, gammaGroundObjectLift_finite_rv_fibres U⟩

structure YinGammaGroundUnmeasuredLiftInput (C : GammaGroundContext M)
    (hc : CanonicalStructure.IsCanonical (M := M)) where
  lift : GammaGroundRVPositiveSemiring hc C.base →+* GammaGroundVFPositiveSemiring hc C.base
  lift_class : ∀ {k : ℕ} (U : GammaGroundRVObject hc C.base k),
    lift (gammaGroundRVSemiringClass U) = gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)
  surjective : Function.Surjective lift
  kernel : gammaGroundRVSpecialCongruence hc C.base = RingCon.ker lift

variable {C : GammaGroundContext M}

def gammaGroundUnmeasuredPositiveIntegral (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFPositiveSemiring hc C.base ≃+* (gammaGroundRVSpecialCongruence hc C.base).Quotient :=
  semiringIntegralFromKernel H.lift H.surjective _ H.kernel

theorem gammaGroundUnmeasuredPositiveIntegral_characterization
    (H : YinGammaGroundUnmeasuredLiftInput C hc) {k : ℕ}
    (A : GammaGroundFiniteVFObject hc C.base) (U : GammaGroundRVObject hc C.base k) :
    gammaGroundUnmeasuredPositiveIntegral H (gammaGroundVFSemiringClass A) =
      (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVSemiringClass U) ↔
      gammaGroundVFSemiringClass A = gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U) := by
  rw [gammaGroundUnmeasuredPositiveIntegral, semiringIntegralFromKernel_characterization, H.lift_class]

@[simp] theorem gammaGroundUnmeasuredPositiveIntegral_lift_class
    (H : YinGammaGroundUnmeasuredLiftInput C hc) {k : ℕ} (U : GammaGroundRVObject hc C.base k) :
    gammaGroundUnmeasuredPositiveIntegral H (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)) =
      (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVSemiringClass U) :=
  (gammaGroundUnmeasuredPositiveIntegral_characterization H (gammaGroundObjectLiftFinite U) U).mpr rfl

theorem gammaGroundUnmeasuredPositiveIntegral_unique (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (e : GammaGroundVFPositiveSemiring hc C.base →+* (gammaGroundRVSpecialCongruence hc C.base).Quotient)
    (he : ∀ {k : ℕ} (U : GammaGroundRVObject hc C.base k),
      e (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)) =
        (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVSemiringClass U)) :
    e = (gammaGroundUnmeasuredPositiveIntegral H).toRingHom := by
  have hcomp : e.comp H.lift = (gammaGroundUnmeasuredPositiveIntegral H).toRingHom.comp H.lift := by
    apply positivePresentationHom_ext (gammaGroundRVSemiringPresentation hc C.base)
    rintro ⟨k, U⟩
    change e (H.lift (gammaGroundRVSemiringClass U)) =
      gammaGroundUnmeasuredPositiveIntegral H (H.lift (gammaGroundRVSemiringClass U))
    rw [H.lift_class]
    exact (he U).trans (gammaGroundUnmeasuredPositiveIntegral_lift_class H U).symm
  apply RingHom.ext
  intro a
  obtain ⟨u, rfl⟩ := H.surjective a
  exact RingHom.congr_fun hcomp u

def gammaGroundUnmeasuredRingIntegral (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFGrothendieckRing hc C.base ≃+*
      GammaGroundRVGrothendieckRing hc C.base ⧸ Ideal.span
        ({gammaGroundRVPrincipalElement hc C.base - 1} : Set (GammaGroundRVGrothendieckRing hc C.base)) :=
  (ringCompletionCongr (gammaGroundUnmeasuredPositiveIntegral H)).trans
    (gammaGroundRVSpecialCompletionEquiv hc C.base)

end DiamondIntegral.Section3
