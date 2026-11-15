import «section 5».NativeProductBijections
import «section 3».GammaGroundRVProductScissors

/-! Actual native cartesian products distribute over the literal tagged
RV coproduct, in arbitrary arities and over the original Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b c : ℕ}

def nativeTaggedProductBijection
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) c)) :
    GammaGroundBijection (gammaGroundRVProductDomain A (gammaGroundRVTaggedUnion C D))
      (gammaGroundRVTaggedUnion (gammaGroundRVProductDomain A C) (gammaGroundRVProductDomain A D)) := by
  let L := (gammaGroundRVLeftTag C c).image
  let R := (gammaGroundRVRightTag D b).image
  let P := gammaGroundRVProductDomain A C
  let Q := gammaGroundRVProductDomain A D
  let f : GammaGroundBijection (gammaGroundRVProductDomain A L) (gammaGroundRVLeftTag P (a+c)).image :=
    (gammaGroundRVLeftTagBijection P (a+c)).comp
      (nativeRawProductBijection (GammaGroundBijection.id A) (gammaGroundRVLeftTagBijection C c).symm)
  let g : GammaGroundBijection (gammaGroundRVProductDomain A R) (gammaGroundRVRightTag Q (a+b)).image :=
    (gammaGroundRVRightTagBijection Q (a+b)).comp
      (nativeRawProductBijection (GammaGroundBijection.id A) (gammaGroundRVRightTagBijection D b).symm)
  have he : (gammaGroundRVProductDomain A (gammaGroundRVTaggedUnion C D)).carrier =
      ((gammaGroundRVProductDomain A L).union (gammaGroundRVProductDomain A R)).carrier :=
    congrArg GammaGroundDefSet.carrier (gammaGroundRVProductDomain_union A L R)
  exact (gammaGroundDisjointUnionBijection f g
    (gammaGroundRVProductDomain_disjoint A L R (gammaGroundRVTaggedImages_disjoint C D))
    (gammaGroundRVTaggedImages_disjoint P Q)).comp (gammaGroundBijectionOfCarrierEq _ _ he)

end DiamondIntegral.Section5
