import «section 6».OrdinaryCentripetalFrames

/-! An actual permitted regularization realizes an ordinary canonical
primitive while retaining the explicit selector for every old label. -/

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
variable (X : OrdinaryUnaryFocusFrame hc A hA q)

include hA in
theorem canonicalTarget_gamma :
    SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier (SpecialTransformations.Section5.canonicalImage A)) :=
  SpecialTransformations.Section5.GammaPrimitiveDefinable.target
    (SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)) (.canonical A) hA

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def afterCanonical
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    OrdinaryUnaryFocusFrame hc (SpecialTransformations.Section5.canonicalImage A)
      (canonicalTarget_gamma (hA := hA)) (1+q) := by
  let L := SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)
  let oldStep := originalBaseOrdinaryMap hc hA (canonicalTarget_gamma (hA := hA))
    (SpecialTransformations.Section5.Primitive.canonical A).toMap
    (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L (.canonical A) hA)
  let f := regularization X.source
  have hf : Function.Bijective f := regularization_bijective X.source
  let W := (regularizeMap X.source).image
  refine {
    source := W
    oldMap := oldStep.comp (X.oldMap.comp (f.inverse hf))
    labels := Fin.addCases (Fin.castAdd q) (fun i => Fin.natAdd 1 (X.labels i))
    point := ?_
    proper := regularization_properInvariant h00 hc hκ hs hv X.source X.proper X.doublyBounded
    doublyBounded := regularized_vfDoublyBounded X.doublyBounded
    tagged := ?_ }
  · intro w
    obtain ⟨p,rfl⟩ := hf.surjective w
    change (oldStep (X.oldMap (f.inverse hf (f p)))).val=_
    rw [Map.inverse_apply]
    apply Prod.ext
    · change (X.oldMap p).val.1=p.val.1
      exact congrArg Prod.fst (X.point p)
    · change (SpecialTransformations.Section5.canonical (X.oldMap p).val).2=
        (regularize p.val).2 ∘ Fin.addCases (Fin.castAdd q) (fun i => Fin.natAdd 1 (X.labels i))
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [SpecialTransformations.Section5.canonical,regularize,Function.comp_apply,
          Fin.addCases_left,Fin.append_left]
        exact congrArg (fun z : Mixed M 1 r => rv M (z.1 i)) (X.point p)
      · simp only [SpecialTransformations.Section5.canonical,regularize,Function.comp_apply,
          Fin.addCases_right,Fin.append_right]
        exact congrFun (congrArg Prod.snd (X.point p)) i
  · rw [show W.carrier=regularize '' X.source.carrier from regularization_carrier _]
    exact regularized_tagged _

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
