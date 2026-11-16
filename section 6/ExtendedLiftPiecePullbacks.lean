import «section 6».MeasuredRVVolumeExtensions
import «section 6».EverywhereMeasuredRVLiftData

/-! Actual pullback of a local lift source through a definable
injection of old labels. The VF tuple is retained exactly and the
local RV label is the prescribed image of the whole old label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def extendedLiftPiecePullback (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Map (rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)) (rvLift A.object) := by
  let W := measuredRVVolumeExtension hc U A D χ hχ
  let X := rvLift (W.object.restrict D hD)
  let f := Map.fst (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S X
  exact (f.pair (χ.comp (liftLabelMap (W.object.restrict D hD)))).corestrict (fun p => by
    let uD := liftLabelMap (W.object.restrict D hD) p
    let u : U.object.domain := ⟨uD.val,hD uD.property⟩
    have hVol : W.object.value u = tupleRV p.val.1 := liftLabelMap_volume (W.object.restrict D hD) p
    have hEqual := measuredRVVolumeExtension_of_mem hc U A D χ hχ u uD.property
    exact ⟨χ uD,rfl,hEqual.symm.trans hVol⟩)

theorem extendedLiftPiecePullback_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)) :
    (extendedLiftPiecePullback hc U A D hD χ hχ p).val =
      (p.val.1,(χ (liftLabelMap ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD) p)).val) := rfl

theorem extendedLiftPiecePullback_label (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)) :
    liftLabelMap A.object (extendedLiftPiecePullback hc U A D hD χ hχ p) =
      χ (liftLabelMap ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD) p) :=
  Subtype.ext rfl

theorem extendedLiftPiecePullback_injective (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Function.Injective (extendedLiftPiecePullback hc U A D hD χ hχ) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : rvLift A.object => z.val.1) hpq
  · have hLabels := congrArg (liftLabelMap A.object) hpq
    rw [extendedLiftPiecePullback_label,extendedLiftPiecePullback_label] at hLabels
    exact congrArg Subtype.val (hχ hLabels)

end DiamondIntegral.Section6
