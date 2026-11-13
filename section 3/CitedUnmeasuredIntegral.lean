import «section 3».VFSemiring
import «section 3».RVGenerators
import «section 3».Lifting
import «section 3».CompletionEquivalences
import «section 2».Bases

/-! Replaceable cited input from Yin [18], Proposition 6.18 and Theorem
6.19, including the following identification of the elementary relation.
This interface specializes the accepted source to a small VF-generated
real substructure. Its generation, characteristic, saturation and
nontrivial-ground-value hypotheses remain explicit. The stronger full
Gamma/imaginary-base formulation and bounded-degree comparisons are separate.

The consequences below are proved relative to the supplied cited input;
they do not provide an independent formalization of the cited paper. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

structure YinUnmeasuredLiftInput (B : Section2.VFGeneratedFieldBase C.base) where
  lift : RVPositiveSemiring (C.base : Set M) →+* VFPositiveSemiring C hc hv
  lift_class : ∀ {k : ℕ} (U : RVObject (M := M) (C.base : Set M) k),
    lift (rvSemiringClass U) = vfSemiringClass C hc hv (objectLiftVF U)
  surjective : Function.Surjective lift
  kernel : rvSpecialCongruence hc (C.base : Set M) = RingCon.ker lift

variable {C hc hv} {B : Section2.VFGeneratedFieldBase C.base}

def unmeasuredPositiveIntegral (H : YinUnmeasuredLiftInput C hc hv B) :
    VFPositiveSemiring C hc hv ≃+* (rvSpecialCongruence hc (C.base : Set M)).Quotient :=
  semiringIntegralFromKernel H.lift H.surjective _ H.kernel

theorem unmeasuredPositiveIntegral_characterization
    (H : YinUnmeasuredLiftInput C hc hv B) {n k : ℕ}
    (A : VFObject (M := M) (C.base : Set M) n) (U : RVObject (M := M) (C.base : Set M) k) :
    unmeasuredPositiveIntegral H (vfSemiringClass C hc hv A) =
      (rvSpecialCongruence hc (C.base : Set M)).mk' (rvSemiringClass U) ↔
      vfSemiringClass C hc hv A = vfSemiringClass C hc hv (objectLiftVF U) := by
  rw [unmeasuredPositiveIntegral, semiringIntegralFromKernel_characterization, H.lift_class]

def unmeasuredRingIntegral (H : YinUnmeasuredLiftInput C hc hv B) :
    VFGrothendieckRing C hc hv ≃+*
      RVGrothendieckRing (C.base : Set M) ⧸ Ideal.span
        ({rvPrincipalElement hc (C.base : Set M) - 1} : Set (RVGrothendieckRing (C.base : Set M))) :=
  (ringCompletionCongr (unmeasuredPositiveIntegral H)).trans
    (rvSpecialCompletionEquiv hc (C.base : Set M))

end DiamondIntegral.Section3
