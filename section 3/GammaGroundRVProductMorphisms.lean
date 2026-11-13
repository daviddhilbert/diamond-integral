import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundBijectionProducts

/-! Genuine same-ground cartesian product bijections between RV objects. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n m k l : ℕ}

def gammaGroundRVPackBijection (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    GammaGroundBijection (A.prod B) (gammaGroundRVProductDomain A B) :=
  ⟨(gammaGroundRVPack A B).toImage, (gammaGroundRVPack A B).toImage_bijective (gammaGroundRVPack_injective A B)⟩

def gammaGroundRVProductBijection {U U' : GammaGroundRVObject hc ground k}
    {V V' : GammaGroundRVObject hc ground l} (f : GammaGroundBijection U.domain U'.domain)
    (g : GammaGroundBijection V.domain V'.domain) :
    GammaGroundBijection (U.product V).domain (U'.product V').domain :=
  (gammaGroundRVPackBijection U'.domain V'.domain).comp
    ((f.prodMap g).comp (gammaGroundRVPackBijection U.domain V.domain).symm)

def gammaGroundRVProductIso {U U' : GammaGroundRVObject hc ground k} {V V' : GammaGroundRVObject hc ground l}
    (f : U ≅ U') (g : V ≅ V') : U.product V ≅ U'.product V' :=
  asIso (show U.product V ⟶ U'.product V' from gammaGroundRVProductBijection f.hom g.hom)

end DiamondIntegral.Section3
