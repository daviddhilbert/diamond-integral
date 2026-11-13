import «section 3».GammaGroundUnitFibreDescent
import «section 3».MonomialValueKernels
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- A full-fibre RV bijection given by a unimodular affine monomial
defines a genuine same-ground Gamma morphism, including its code lift. -/
def gammaGroundGammaSingleHomOfAffineMonomial (G H : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H))
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det) (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hF : ∀ u, (F.map u).val = c * integerMonomialMap A u.val) :
    GammaGroundGammaHom (GammaGroundGammaObject.single G) (GammaGroundGammaObject.single H) := by
  apply gammaGroundGammaSingleHomOfUnitBijection G H F
  intro u v
  rw [hF u,hF v]
  exact (affineMonomial_value_kernel_iff (rvUnitValueHom (M := M)) A hA c u.val v.val).symm
end DiamondIntegral.Section3
