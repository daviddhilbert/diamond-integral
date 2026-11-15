import «section 5».RelativePointProductSemiring
import «section 5».OriginalTaggedTotalValues

/-! Total native RV values are an additive invariant of the actual
relative family ring. This construction uses no multiplicativity of
the forgetful map for products sharing their parameter base. -/
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
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem relativeRVEmptyTotal
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    ((RelativeRVFamily.empty B p).total X).carrier = ∅ := by
  ext u
  constructor
  · exact fun h => h.1
  · exact False.elim

def relativeRVTotalInvariant
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    Invariant (relativePointPresentation X) (A := RESDimensionFreeReduction.Ring B) where
  toFun F := nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (F.total X)
  iso h := original_rv_total_value_of_pointwise_bijections h00 linear hκ hs hr hγ hΓ kind X _ _ h
  empty := nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (relativeRVEmptyTotal X)
  scissor := by
    intro F G H I h
    rcases h with ⟨rfl,rfl⟩
    have h0 : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        ((RelativeRVFamily.empty B p).total X) = 0 :=
      nativeRVSetValue_of_empty h00 linear hκ hs hr hγ hΓ kind _ (relativeRVEmptyTotal X)
    rw [h0,add_zero]
    exact original_tagged_total_value h00 linear hκ hs hr hγ hΓ kind X H.2 I.2

def nativeRelativeRVForget
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    RelativeRVFamilyRing X →+ RESDimensionFreeReduction.Ring B :=
  Algebra.GrothendieckAddGroup.lift
    (lift (relativePointPresentation X) (relativeRVTotalInvariant h00 linear hκ hs hr hγ hΓ kind X))

theorem nativeRelativeRVForget_class
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X (relativeRVFamilyClass X F) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (F.total X) :=
  (Algebra.GrothendieckAddGroup.lift_apply_of
    (lift (relativePointPresentation X) (relativeRVTotalInvariant h00 linear hκ hs hr hγ hΓ kind X))
      (of (relativePointPresentation X) F)).trans
        (lift_of (relativePointPresentation X) (relativeRVTotalInvariant h00 linear hκ hs hr hγ hΓ kind X) F)

end DiamondIntegral.Section5
