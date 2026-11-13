import «section 3».GammaGroundRVCoproductMaps
import «section 3».GammaGroundMeasuredRVScissors

/-! Genuine measured RV disjoint unions retain the original labels
and the full Gamma form on each summand. -/
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

def GammaGroundMeasuredRVObject.coprod (U V : GammaGroundMeasuredRVObject hc ground k) :
    GammaGroundMeasuredRVObject hc ground k where
  underlying := U.underlying.coprod V.underlying
  form := (U.form.comp (gammaGroundRVUntagLeft U.underlying.domain V.underlying.arity)).union
    (V.form.comp (gammaGroundRVUntagRight V.underlying.domain U.underlying.arity))

theorem gammaGroundMeasuredRVCoprod_form_left (U V : GammaGroundMeasuredRVObject hc ground k)
    (a : U.underlying.domain) :
    gammaGroundFormValue (U.coprod V).form (gammaGroundRVCoprodLeft U.underlying V.underlying a) =
      gammaGroundFormValue U.form a := by
  have he : (U.coprod V).form (gammaGroundRVCoprodLeft U.underlying V.underlying a) = U.form a := by
    change ((U.form.comp (gammaGroundRVUntagLeft U.underlying.domain V.underlying.arity)).union
      (V.form.comp (gammaGroundRVUntagRight V.underlying.domain U.underlying.arity)))
      ⟨((gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage a).val,
        Or.inl ((gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage a).property⟩ = _
    rw [GammaGroundMap.union_on_left]
    exact congrArg U.form (GammaGroundMap.inverse_apply _ _ a)
  exact congrArg (fun z => cast (gammaCarrier hc) z.val) he

theorem gammaGroundMeasuredRVCoprod_form_right (U V : GammaGroundMeasuredRVObject hc ground k)
    (b : V.underlying.domain) :
    gammaGroundFormValue (U.coprod V).form (gammaGroundRVCoprodRight U.underlying V.underlying b) =
      gammaGroundFormValue V.form b := by
  have he : (U.coprod V).form (gammaGroundRVCoprodRight U.underlying V.underlying b) = V.form b := by
    change ((U.form.comp (gammaGroundRVUntagLeft U.underlying.domain V.underlying.arity)).union
      (V.form.comp (gammaGroundRVUntagRight V.underlying.domain U.underlying.arity)))
      ⟨((gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage b).val,
        Or.inr ((gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage b).property⟩ = _
    rw [GammaGroundMap.union_on_right _ _ (gammaGroundRVTaggedImages_disjoint U.underlying.domain V.underlying.domain)]
    exact congrArg V.form (GammaGroundMap.inverse_apply _ _ b)
  exact congrArg (fun z => cast (gammaCarrier hc) z.val) he

theorem gammaGroundMeasuredRVCoprod_combined_left (U V : GammaGroundMeasuredRVObject hc ground k)
    (a : U.underlying.domain) :
    (U.coprod V).combinedWeight (gammaGroundRVCoprodLeft U.underlying V.underlying a) = U.combinedWeight a := by
  have ht : (U.coprod V).underlying.target
      (gammaGroundRVCoprodLeft U.underlying V.underlying a) = U.underlying.target a := by
    funext i
    apply Subtype.ext
    exact congrArg (fun t => t.val i) (gammaGroundRVCoprod_volume_left U.underlying V.underlying a)
  unfold GammaGroundMeasuredRVObject.combinedWeight
  rw [gammaGroundMeasuredRVCoprod_form_left, ht]

theorem gammaGroundMeasuredRVCoprod_combined_right (U V : GammaGroundMeasuredRVObject hc ground k)
    (b : V.underlying.domain) :
    (U.coprod V).combinedWeight (gammaGroundRVCoprodRight U.underlying V.underlying b) = V.combinedWeight b := by
  have ht : (U.coprod V).underlying.target
      (gammaGroundRVCoprodRight U.underlying V.underlying b) = V.underlying.target b := by
    funext i
    apply Subtype.ext
    exact congrArg (fun t => t.val i) (gammaGroundRVCoprod_volume_right U.underlying V.underlying b)
  unfold GammaGroundMeasuredRVObject.combinedWeight
  rw [gammaGroundMeasuredRVCoprod_form_right, ht]

end DiamondIntegral.Section3
