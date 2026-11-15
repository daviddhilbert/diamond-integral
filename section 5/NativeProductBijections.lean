import «section 5».NativeUnderlyingBijections
import «section 5».NativeSetBijections
import «section 5».RESSetProductClasses
import «section 3».GammaGroundRVProductMorphisms
import «section 3».GammaGroundRVProductLaws

/-! Literal native schema products carry actual original-base bijections
to native cartesian products, independently of the chosen label degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge Section3RVRoundtripBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeRawProductBijection {a b c d : ℕ}
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}
    {C : GammaGroundDefSet hc B (rawRVSpace (M := M) b)}
    {D : GammaGroundDefSet hc B (rawRVSpace (M := M) c)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) d)}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection C E) :
    GammaGroundBijection (gammaGroundRVProductDomain A C) (gammaGroundRVProductDomain D E) :=
  (gammaGroundRVPackBijection D E).comp ((f.prodMap g).comp (gammaGroundRVPackBijection A C).symm)

def nativeSchemaProductBijection {p a b : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    GammaGroundBijection ((F.product G).object hc z (F.product_valid hc G z hF hG)).obj.domain
      ((F.object hc z hF).obj.product (G.object hc z hG).obj).domain := by
  let U := (F.object hc z hF).obj
  let V := (G.object hc z hG).obj
  let S := ((F.product G).object hc z (F.product_valid hc G z hF hG)).obj
  exact (gammaGroundRVProductCommBijection V U).comp
    ((gammaGroundRVProductBijection (native_chart V) (native_chart U)).comp
      ((Section3RVBasicClasses.nativeProductIso (F.chart hc z hF).toChart (G.chart hc z hG).toChart).symm.comp
        ((nativeUnderlyingBijection (F.productIso hc G z hF hG)).comp (native_chart S).symm)))

end DiamondIntegral.Section5
