import «section 5».RelativePointPresentation
import «section 5».NativeTaggedProductBijections
import «section 5».OriginalTaggedRowPresentations
import «section 5».AdditivePresentationMultiplication

/-! Actual relative RV products and tagged sums give a positive
commutative semiring. All product laws use actual parameter-row
bijections, rather than equality in a fibre RES quotient. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

def originalRVRowProductSumBijection (F G H : RelativeRVFamily B p) (z : Fin p → M) :
    GammaGroundBijection (originalRVRowDomain hc (F.blockProduct (G.sum H)).2 z)
      (originalRVRowDomain hc ((F.blockProduct G).sum (F.blockProduct H)).2 z) :=
  (originalRVRowTaggedBijection (F.blockProduct G).2 (F.blockProduct H).2 z).symm.comp
    ((gammaGroundRVTaggedUnionBijection
      (originalRVRowProductBijection F.2 G.2 z).symm
      (originalRVRowProductBijection F.2 H.2 z).symm).comp
        ((nativeTaggedProductBijection (originalRVRowDomain hc F.2 z)
          (originalRVRowDomain hc G.2 z) (originalRVRowDomain hc H.2 z)).comp
            ((nativeRawProductBijection (GammaGroundBijection.id (originalRVRowDomain hc F.2 z))
              (originalRVRowTaggedBijection G.2 H.2 z)).comp
                (originalRVRowProductBijection F.2 (G.sum H).2 z))))

theorem relativePointwiseIso_product_sum
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G H : RelativeRVFamily B p) :
    relativePointwiseIso X (F.blockProduct (G.sum H)) ((F.blockProduct G).sum (F.blockProduct H)) :=
  fun x => ⟨originalRVRowProductSumBijection F G H (rvValues x.val)⟩

def relativePointProductInvariant
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    Invariant (relativePointPresentation X) (A := SpecialTransformations.Section4.PositiveAdditiveGrothendieck.KPlus (relativePointPresentation X)) where
  toFun G := of (relativePointPresentation X) (F.blockProduct G)
  iso h := of_iso (relativePointPresentation X)
    (relativePointwiseIso_product (relativePointwiseIso_refl X F) h)
  empty := (of_iso (relativePointPresentation X) (relativePointwiseIso_product_empty X F)).trans
    (of_empty (relativePointPresentation X))
  scissor := by
    intro G H I J h
    rcases h with ⟨rfl,rfl⟩
    have h0 : of (relativePointPresentation X) (F.blockProduct (RelativeRVFamily.empty B p)) = 0 :=
      (of_iso (relativePointPresentation X) (relativePointwiseIso_product_empty X F)).trans
        (of_empty (relativePointPresentation X))
    have he := of_iso (relativePointPresentation X) (relativePointwiseIso_product_sum X F I J)
    change of (relativePointPresentation X) (F.blockProduct (I.sum J)) +
      of (relativePointPresentation X) (F.blockProduct (RelativeRVFamily.empty B p)) = _
    rw [h0,add_zero,he,relativePointClass_sum]

def relativePointProductData
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) : PositiveProductData (relativePointPresentation X) where
  sum := RelativeRVFamily.sum
  sum_class := relativePointClass_sum X
  mul := RelativeRVFamily.blockProduct
  one := RelativeRVFamily.one B p
  productInvariant := relativePointProductInvariant X
  product_value := fun _ _ => rfl
  comm F G := of_iso (relativePointPresentation X) (relativePointwiseIso_product_comm X F G)
  assoc F G H := of_iso (relativePointPresentation X) (relativePointwiseIso_product_assoc X F G H)
  one_left F := of_iso (relativePointPresentation X) (relativePointwiseIso_product_one X F)

abbrev RelativeRVPositive
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) := SpecialTransformations.Section4.PositiveAdditiveGrothendieck.KPlus (relativePointPresentation X)

instance relativeRVPositiveCommSemiring
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) : CommSemiring (RelativeRVPositive X) :=
  positiveProductCommSemiring (relativePointProductData X)

abbrev RelativeRVFamilyRing
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) := Algebra.GrothendieckAddGroup (RelativeRVPositive X)

def relativeRVFamilyClass
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) : RelativeRVFamilyRing X :=
  Algebra.GrothendieckAddGroup.of (of (relativePointPresentation X) F)

theorem relativeRVCompletedClass_product
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) :
    relativeRVFamilyClass X (F.blockProduct G) = relativeRVFamilyClass X F * relativeRVFamilyClass X G := by
  unfold relativeRVFamilyClass
  rw [Algebra.GrothendieckAddGroup.of_mul_of]
  exact congrArg Algebra.GrothendieckAddGroup.of
    ((relativePointProductData X).bilinear_of_of F G).symm

theorem relativeRVCompletedClass_sum
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) :
    relativeRVFamilyClass X (F.sum G) = relativeRVFamilyClass X F + relativeRVFamilyClass X G := by
  unfold relativeRVFamilyClass
  rw [relativePointClass_sum,map_add]

end DiamondIntegral.Section5
