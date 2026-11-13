import «section 3».GammaGroundRVCoproducts

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundRVCoprodLeft (U V : GammaGroundRVObject hc ground k) : GammaGroundMap U.domain (U.coprod V).domain :=
  (GammaGroundMap.inclusion (show (gammaGroundRVLeftTag U.domain V.arity).image.carrier ⊆
    (U.coprod V).domain.carrier from fun _ h => Or.inl h)).comp (gammaGroundRVLeftTag U.domain V.arity).toImage

def gammaGroundRVCoprodRight (U V : GammaGroundRVObject hc ground k) : GammaGroundMap V.domain (U.coprod V).domain :=
  (GammaGroundMap.inclusion (show (gammaGroundRVRightTag V.domain U.arity).image.carrier ⊆
    (U.coprod V).domain.carrier from fun _ h => Or.inr h)).comp (gammaGroundRVRightTag V.domain U.arity).toImage

theorem gammaGroundRVCoprod_volume_left (U V : GammaGroundRVObject hc ground k) (a : U.domain) :
    (U.coprod V).volume (gammaGroundRVCoprodLeft U V a) = U.volume a := by
  change ((U.volume.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (V.volume.comp (gammaGroundRVUntagRight V.domain U.arity)))
    ⟨((gammaGroundRVLeftTag U.domain V.arity).toImage a).val,
      Or.inl ((gammaGroundRVLeftTag U.domain V.arity).toImage a).property⟩ = _
  rw [GammaGroundMap.union_on_left]
  exact congrArg U.volume (GammaGroundMap.inverse_apply _ _ a)

theorem gammaGroundRVCoprod_volume_right (U V : GammaGroundRVObject hc ground k) (b : V.domain) :
    (U.coprod V).volume (gammaGroundRVCoprodRight U V b) = V.volume b := by
  change ((U.volume.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (V.volume.comp (gammaGroundRVUntagRight V.domain U.arity)))
    ⟨((gammaGroundRVRightTag V.domain U.arity).toImage b).val,
      Or.inr ((gammaGroundRVRightTag V.domain U.arity).toImage b).property⟩ = _
  rw [GammaGroundMap.union_on_right _ _ (gammaGroundRVTaggedImages_disjoint U.domain V.domain)]
  exact congrArg V.volume (GammaGroundMap.inverse_apply _ _ b)

end DiamondIntegral.Section3
