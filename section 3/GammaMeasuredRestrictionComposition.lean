import «section 3».GammaGroundMeasuredVFData
import «section 3».GammaFixedPrefixProducts

/-! Iterated literal restrictions retain the original Gamma form and
agree with the direct restriction to the final domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaMeasuredVFRestriction_trans_eq
    (U : GammaGroundMeasuredVFData hc B k)
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hD : D.carrier ⊆ U.domain.carrier)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hAD : A.carrier ⊆ D.carrier)
    (E : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hE : E.carrier ⊆ U.domain.carrier)
    (hAE : A.carrier = E.carrier) :
    (U.restrict D hD).restrict A hAD = U.restrict E hE := by
  have hA : A = E := gammaGroundDefSet_eq_of_carrier_eq hAE
  subst A
  rfl

end DiamondIntegral.Section3
