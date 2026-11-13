import «section 3».RVFormGraphs
import «section 3».MeasuredVFScissors
import «section 3».Lifting

/-! The measured object lift of Notation 3.21, in every degree. Its form
is literally the pullback along the original RV label. Object lifting does
not require generation of the base; class descent is a separate theorem. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def objectLiftLabel (U : RVObject (M := M) S k) : Map (objectLift U) U.domain :=
  (Map.snd (rawVFSpace k) (rawRVSpace U.arity) S (objectLift U)).corestrict
    (fun p => by
      obtain ⟨u, hu, _⟩ := p.property
      change p.val.2 ∈ U.domain.carrier
      exact hu ▸ u.property)

@[simp] theorem objectLiftLabel_value (U : RVObject (M := M) S k) (p : objectLift U) :
    (objectLiftLabel U p).val = p.val.2 := rfl

def measuredLiftForm (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) : GammaVolumeForm hc (objectLift U.underlying) :=
  (U.form.toGammaVolumeForm hc).comp (objectLiftLabel U.underlying)

@[simp] theorem measuredLiftForm_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (p : objectLift U.underlying) :
    gammaFormValue (measuredLiftForm hc U) p = U.form.toFun (objectLiftLabel U.underlying p) := rfl

def measuredObjectLift (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    ∀ k, MeasuredRVObject (M := M) (C.base : Set M) k → MeasuredVFObject C hc k
  | 0, U => {
      arity := U.underlying.arity
      domain := objectLift U.underlying
      finite := objectLift_finite_rv_fibres U.underlying
      form := measuredLiftForm hc U }
  | k + 1, U => {
      arity := U.underlying.arity
      domain := objectLift U.underlying
      finite := objectLift_finite_rv_fibres U.underlying
      form := measuredLiftForm hc U }

end DiamondIntegral.Section3
