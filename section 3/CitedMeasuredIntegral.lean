import «section 3».MeasuredVFSemiring
import «section 3».MeasuredRVGenerators
import «section 3».MeasuredLifting
import «section 3».CompletionEquivalences
import «section 3».QuotientIntegral
import «section 2».Bases

/-! Replaceable Gamma-volume comparison from accepted [18], Theorems
2.35–2.36, the opening extension of Section 7 to the relevant volume
categories, Propositions 7.8–7.10 and Theorem 7.13. The actual pointwise
Gamma RV category and essential Gamma VF category are retained.
These interfaces specialize to a small VF-generated real substructure;
no independent formal proof of the cited paper is asserted. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (VFType (M := M))]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))

structure YinMeasuredLiftInput (B : Section2.VFGeneratedFieldBase C.base) where
  lift : MeasuredRVPositiveSemiring hc (C.base : Set M) →+* MeasuredVFPositiveSemiring C hc
  lift_class : ∀ {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k),
    lift (measuredRVSemiringClass hc U) =
      measuredVFObjectSemiringClass C hc (measuredObjectLift hc C k U)
  surjective : Function.Surjective lift
  kernel : measuredRVSpecialCongruence hc (C.base : Set M) = RingCon.ker lift

def measuredRVFixedSpecialHom (k : ℕ) : MeasuredRVKPlus hc (C.base : Set M) k →+
    (measuredRVSpecialCongruence hc (C.base : Set M)).Quotient :=
  (measuredRVSpecialCongruence hc (C.base : Set M)).mk'.toAddMonoidHom.comp
    (measuredRVKPlusToSemiring hc)

def measuredRVFixedSpecialCongruence (k : ℕ) : AddCon (MeasuredRVKPlus hc (C.base : Set M) k) :=
  AddCon.ker (measuredRVFixedSpecialHom C hc k)

structure YinDegreeMeasuredLiftInput (B : Section2.VFGeneratedFieldBase C.base) where
  lift : ∀ k, MeasuredRVKPlus hc (C.base : Set M) k →+ MeasuredVFKPlus C hc k
  lift_class : ∀ {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k),
    lift k (measuredRVClass hc U) =
      positiveClass (measuredVFPresentation C hc k) (measuredObjectLift hc C k U)
  surjective : ∀ k, Function.Surjective (lift k)
  kernel : ∀ k, measuredRVFixedSpecialCongruence C hc k = AddCon.ker (lift k)

variable {C hc} {B : Section2.VFGeneratedFieldBase C.base}

def measuredPositiveIntegral (H : YinMeasuredLiftInput C hc B) :
    MeasuredVFPositiveSemiring C hc ≃+*
      (measuredRVSpecialCongruence hc (C.base : Set M)).Quotient :=
  semiringIntegralFromKernel H.lift H.surjective _ H.kernel

theorem measuredPositiveIntegral_characterization (H : YinMeasuredLiftInput C hc B) {k : ℕ}
    (A : MeasuredVFObject C hc k) (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    measuredPositiveIntegral H (measuredVFObjectSemiringClass C hc A) =
      (measuredRVSpecialCongruence hc (C.base : Set M)).mk' (measuredRVSemiringClass hc U) ↔
      measuredVFObjectSemiringClass C hc A =
        measuredVFObjectSemiringClass C hc (measuredObjectLift hc C k U) := by
  rw [measuredPositiveIntegral, semiringIntegralFromKernel_characterization, H.lift_class]

def measuredRingIntegral (H : YinMeasuredLiftInput C hc B) :
    MeasuredVFGrothendieckRing C hc ≃+*
      MeasuredRVGrothendieckRing hc (C.base : Set M) ⧸ Ideal.span
        ({measuredRVPrincipalElement hc (C.base : Set M)} :
          Set (MeasuredRVGrothendieckRing hc (C.base : Set M))) :=
  (ringCompletionCongr (measuredPositiveIntegral H)).trans
    (measuredRVSpecialCompletionEquiv hc (C.base : Set M))

def degreeMeasuredIntegral (H : YinDegreeMeasuredLiftInput C hc B) (k : ℕ) :
    MeasuredVFKPlus C hc k ≃+ (measuredRVFixedSpecialCongruence C hc k).Quotient :=
  integralFromKernel (H.lift k) (H.surjective k) _ (H.kernel k)

theorem degreeMeasuredIntegral_characterization (H : YinDegreeMeasuredLiftInput C hc B)
    {k : ℕ} (A : MeasuredVFObject C hc k) (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    degreeMeasuredIntegral H k (positiveClass (measuredVFPresentation C hc k) A) =
      (measuredRVFixedSpecialCongruence C hc k).mk' (measuredRVClass hc U) ↔
      positiveClass (measuredVFPresentation C hc k) A =
        positiveClass (measuredVFPresentation C hc k) (measuredObjectLift hc C k U) := by
  rw [degreeMeasuredIntegral, integralFromKernel_characterization, H.lift_class]

end DiamondIntegral.Section3
