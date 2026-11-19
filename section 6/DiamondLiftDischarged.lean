import «section 6».DiamondLiftHomomorphism
import «section 5».GammaQEFiniteLaws

/-! Corollary 6.37 (`L:sur:c`) without the unary Γ rational-affine input. That
input is the theorem `Section5.GammaQE.gamma_piecewise_rational_affine`, proved
from RV quantifier elimination with no further hypotheses. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Corollary 6.37: the lift homomorphism is surjective, with the Γ input discharged. -/
theorem liftHom_surjective_discharged (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    Function.Surjective (liftHom k G h00 hc (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
      hκ hs hv T B₀ hsmall hΓ hnt) :=
  liftHom_surjective h00 hc _ hκ hs hv T B₀ hsmall hΓ hnt

end DiamondIntegral.Section6.DiamondLiftHomomorphism
