import «section 3».RVCoproducts
import «section 3».RVFormGraphs
import «section 3».MeasuredRVScissors

/-! Genuine tagged disjoint unions of pointwise Gamma-measured RV
objects, with the original volume form on each summand. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def measuredRVCoprodForm (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) : GammaVolumeForm hc (U.underlying.coprod V.underlying).domain :=
  ((U.form.toGammaVolumeForm hc).comp (rvUntagLeft U.underlying.domain V.underlying.arity)).union
    ((V.form.toGammaVolumeForm hc).comp (rvUntagRight V.underlying.domain U.underlying.arity))

def MeasuredRVObject.coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) : MeasuredRVObject S k :=
  ⟨U.underlying.coprod V.underlying, (measuredRVCoprodForm hc U V).toRVVolumeForm hc⟩

theorem measuredRVCoprod_form_left (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) (a : U.underlying.domain) :
    (U.coprod hc V).form.toFun
      (rvCoprodLeftMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj a) = U.form.toFun a := by
  have h : measuredRVCoprodForm hc U V
      (rvCoprodLeftMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj a) =
        U.form.toGammaVolumeForm hc a := by
    change (((U.form.toGammaVolumeForm hc).comp (rvUntagLeft U.underlying.domain V.underlying.arity)).union
      ((V.form.toGammaVolumeForm hc).comp (rvUntagRight V.underlying.domain U.underlying.arity)))
        ⟨((rvLeftTagMap U.underlying.domain V.underlying.arity).toImage a).val,
          Or.inl ((rvLeftTagMap U.underlying.domain V.underlying.arity).toImage a).property⟩ = _
    rw [Map.union_on_left]
    exact congrArg (U.form.toGammaVolumeForm hc) (Map.inverse_apply _ _ a)
  exact congrArg (fun z : DefSet.univ (volumeGammaSpace hc) S => z.val) h

theorem measuredRVCoprod_form_right (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) (b : V.underlying.domain) :
    (U.coprod hc V).form.toFun
      (rvCoprodRightMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj b) = V.form.toFun b := by
  have h : measuredRVCoprodForm hc U V
      (rvCoprodRightMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj b) =
        V.form.toGammaVolumeForm hc b := by
    change (((U.form.toGammaVolumeForm hc).comp (rvUntagLeft U.underlying.domain V.underlying.arity)).union
      ((V.form.toGammaVolumeForm hc).comp (rvUntagRight V.underlying.domain U.underlying.arity)))
        ⟨((rvRightTagMap V.underlying.domain U.underlying.arity).toImage b).val,
          Or.inr ((rvRightTagMap V.underlying.domain U.underlying.arity).toImage b).property⟩ = _
    rw [Map.union_on_right _ _ (rvTaggedImages_disjoint U.underlying.domain V.underlying.domain)]
    exact congrArg (V.form.toGammaVolumeForm hc) (Map.inverse_apply _ _ b)
  exact congrArg (fun z : DefSet.univ (volumeGammaSpace hc) S => z.val) h

theorem measuredRVCoprod_combined_left (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) (a : U.underlying.domain) :
    (U.coprod hc V).combinedWeight
      (rvCoprodLeftMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj a) = U.combinedWeight a := by
  have ht : (U.underlying.coprod V.underlying).target
      (rvCoprodLeftMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj a) = U.underlying.target a := by
    funext i
    apply Subtype.ext
    exact congrFun (rvCoprod_value_left U.underlying.toCompanion.obj V.underlying.toCompanion.obj a) i
  unfold MeasuredRVObject.combinedWeight
  rw [measuredRVCoprod_form_left]
  change U.form.toFun a * (∏ i, Section2.rvFiniteValue ((U.underlying.coprod V.underlying).target _ i)) = _
  rw [ht]

theorem measuredRVCoprod_combined_right (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) (b : V.underlying.domain) :
    (U.coprod hc V).combinedWeight
      (rvCoprodRightMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj b) = V.combinedWeight b := by
  have ht : (U.underlying.coprod V.underlying).target
      (rvCoprodRightMap U.underlying.toCompanion.obj V.underlying.toCompanion.obj b) = V.underlying.target b := by
    funext i
    apply Subtype.ext
    exact congrFun (rvCoprod_value_right U.underlying.toCompanion.obj V.underlying.toCompanion.obj b) i
  unfold MeasuredRVObject.combinedWeight
  rw [measuredRVCoprod_form_right]
  change V.form.toFun b * (∏ i, Section2.rvFiniteValue ((U.underlying.coprod V.underlying).target _ i)) = _
  rw [ht]

end DiamondIntegral.Section3
