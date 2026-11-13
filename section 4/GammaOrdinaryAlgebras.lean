import «section 4».GammaOrdinaryFiniteMaps
import «section 4».RESOrdinaryReduction
import «section 4».RVOrdinaryMaps

/-! Actual ordinary finite-Gamma coefficient algebras for the ordinary
RES/Gamma tensor and its RV comparison and RES target. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Coeff (B : Base (M := M)) := GammaOrdinaryFiniteRing.Ring B

instance resAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RESOrdinaryRing.Ring B) :=
  (GammaOrdinaryFiniteMaps.sharp B).toAlgebra
instance gammaAlgebra (B : Base (M := M)) : Algebra (Coeff B) (GammaOrdinaryRing.Ring B) :=
  (GammaOrdinaryFiniteMaps.full B).toAlgebra
instance rvAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RVOrdinaryRing.Ring B) :=
  ((RVOrdinaryMaps.ofRES B).comp (GammaOrdinaryFiniteMaps.sharp B)).toAlgebra
instance targetAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RESOrdinaryReduction.ReducedRing B) :=
  ((RESOrdinaryReduction.quotient B).comp (GammaOrdinaryFiniteMaps.sharp B)).toAlgebra

end DiamondIntegral.Section4.GammaOrdinaryAlgebras
