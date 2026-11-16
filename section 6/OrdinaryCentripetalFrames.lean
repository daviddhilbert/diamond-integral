import «section 6».OrdinaryNoCoreStepValues
import «section 6».CoordinateCoreFormConstancy

/-! The actual no-core finite-aperture step and regularization supply
the next ordinary-chain frame, with an explicit retained-label selector
and exact old component values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)

include hA hD in
theorem centripetalTarget_gamma :
    SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier D.etaImage) :=
  SpecialTransformations.Section5.GammaPrimitiveDefinable.target
    (SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)) (.centripetal D) ⟨hA,hD⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def afterCentripetal
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : CentripetalData (G := G) X.source)
    (hCoord : E.coordinate=0) (hActive : E.activeTags=X.activeTags D hD)
    (hFocus : ∀ x u,E.focus x u=(X.focusData D hD).focus u)
    (hCore : ∀ p ∈ X.source.carrier,E.core p=false) :
    OrdinaryUnaryFocusFrame hc D.etaImage (centripetalTarget_gamma (hA := hA) D hD) (1+(1+q)) := by
  let L := SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)
  let oldStep := originalBaseOrdinaryMap hc hA (centripetalTarget_gamma (hA := hA) D hD)
    (SpecialTransformations.Section5.Primitive.centripetal D).toMap
    (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L (.centripetal D) ⟨hA,hD⟩)
  let f := centripetalStepMap E
  have hf : Function.Bijective f := centripetalStepMap_bijective E h00
  let W := (regularizeMap E.map.image).image
  refine {
    source := W
    oldMap := oldStep.comp (X.oldMap.comp (f.inverse hf))
    labels := fun i => Fin.natAdd 1 (Fin.natAdd 1 (X.labels i))
    point := ?_
    proper := regularization_properInvariant h00 hc hκ hs hv E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
    doublyBounded := regularized_vfDoublyBounded E.image_vfDoublyBounded
    tagged := ?_ }
  · intro w
    obtain ⟨p,rfl⟩ := hf.surjective w
    change (oldStep (X.oldMap (f.inverse hf (f p)))).val=_
    rw [Map.inverse_apply]
    apply Prod.ext
    · change (D.toFocusGeometry.eta (X.oldMap p).val).1=(E.point p.val).1
      exact (X.component_field_matches_ordinary D hD E hCoord hActive hFocus hCore p).symm
    · change (D.toFocusGeometry.eta (X.oldMap p).val).2=_
      rw [D.toFocusGeometry.eta_labels]
      funext i
      change (X.oldMap p).val.2 i=
        (regularize (E.point p.val)).2 (Fin.natAdd 1 (Fin.natAdd 1 (X.labels i)))
      simp only [regularize,Fin.append_right,CentripetalData.point]
      exact congrFun (congrArg Prod.snd (X.point p)) i
  · rw [show W.carrier=regularize '' E.map.image.carrier from regularization_carrier _]
    exact regularized_tagged _

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
