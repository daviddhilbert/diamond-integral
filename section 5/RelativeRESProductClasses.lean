import «section 5».RelativePointProductSemiring
import «section 5».NativeProductBijections

/-! Literal RES-expression products represent the canonical product in
the relative family ring whenever their actual fibre objects are valid. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

def nativeRESRowBijection (F : RESSetSchema B p a (fun _ => .rv)) (z : Fin p → M)
    (hF : F.Valid hc z) :
    GammaGroundBijection (originalRVRowDomain hc F.domain z) (F.object hc z hF).obj.domain :=
  gammaGroundBijectionOfCarrierEq _ _ rfl

def relativeRESProductRowBijection
    (F : RESSetSchema B p a (fun _ => .rv)) (G : RESSetSchema B p b (fun _ => .rv))
    (z : Fin p → M) (hF : F.Valid hc z) (hG : G.Valid hc z) :
    GammaGroundBijection (originalRVRowDomain hc (F.product G).domain z)
      (originalRVRowDomain hc (originalDomainProduct F.domain G.domain) z) :=
  (originalRVRowProductBijection F.domain G.domain z).symm.comp
    ((nativeRawProductBijection (nativeRESRowBijection F z hF).symm (nativeRESRowBijection G z hG).symm).comp
      ((nativeSchemaProductBijection F G z hF hG).comp
        (nativeRESRowBijection (F.product G) z (F.product_valid hc G z hF hG))))

theorem relativeRVCompletedClass_iso
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) {F G : RelativeRVFamily B p}
    (h : relativePointwiseIso X F G) : relativeRVFamilyClass X F = relativeRVFamilyClass X G :=
  congrArg Algebra.GrothendieckAddGroup.of (of_iso (relativePointPresentation X) h)

theorem relativeRESProduct_class
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : RESSetSchema B p a (fun _ => .rv)) (G : RESSetSchema B p b (fun _ => .rv))
    (hF : ∀ x : X, F.Valid hc (rvValues x.val)) (hG : ∀ x : X, G.Valid hc (rvValues x.val)) :
    relativeRVFamilyClass X ⟨b+a,(F.product G).domain⟩ =
      relativeRVFamilyClass X ⟨a,F.domain⟩ * relativeRVFamilyClass X ⟨b,G.domain⟩ :=
  (relativeRVCompletedClass_iso X (fun x => ⟨relativeRESProductRowBijection F G _ (hF x) (hG x)⟩)).trans
    (relativeRVCompletedClass_product X ⟨a,F.domain⟩ ⟨b,G.domain⟩)

end DiamondIntegral.Section5
