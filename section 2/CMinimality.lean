import «section 2».Conventions
import Section3.GammaBaseCMinimal

/-! C-minimality with the author-approved parameter distinction (R027).
The original set is defined over the ground base. Individual component
discs may need additional names; no ground-definability of each is asserted.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The C-minimality sentence for a set definable over the fixed real base. -/
theorem c_minimal_ground_base (S A : Set M) (hA : DefinableAt S .vf A) :
    IsBoolComb {C | IsBall C} A := hA.isBoolComb_balls

/-- The same decomposition with genuine Gamma parameters in the ground
base. Disc names in the decomposition need not belong to that base. -/
theorem c_minimal_parameter_base (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) : IsBoolComb {C | IsBall C} A :=
  GammaParameters.c_minimal_gamma_base B A hA

end DiamondIntegral.Section2
