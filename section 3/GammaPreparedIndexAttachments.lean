import «section 5».NativeVFKeyAttachments
import «section 5».NativeMixedCoordinateMaps

/-! Attaching the VF base's RV key and retaining every old RV label
produces the literal labels used by an indexed presentation. This is
an injective original-language map fixing the entire VF tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k l a : ℕ}

def gammaPreparedIndexAssoc (p l a : ℕ) : Fin ((p+l)+a) → Fin (p+(l+a)) :=
  Fin.addCases (Fin.addCases (Fin.castAdd (l+a)) (fun j => Fin.natAdd p (Fin.castAdd a j)))
    (fun j => Fin.natAdd p (Fin.natAdd l j))

theorem gammaPreparedIndexAssoc_surjective (p l a : ℕ) : Function.Surjective (gammaPreparedIndexAssoc p l a) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact ⟨Fin.castAdd a (Fin.castAdd l j),by simp only [gammaPreparedIndexAssoc,Fin.addCases_left,Fin.addCases_right]⟩
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      exact ⟨Fin.castAdd a (Fin.natAdd p j),by simp only [gammaPreparedIndexAssoc,Fin.addCases_left,Fin.addCases_right]⟩
    · intro j
      exact ⟨Fin.natAdd (p+l) j,by simp only [gammaPreparedIndexAssoc,Fin.addCases_left,Fin.addCases_right]⟩

def gammaPreparedIndexAttachment (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+a))) :
    GammaGroundMap Y (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+k) ((p+l)+a))) :=
  (Section5.nativeMixedCoordinateMap (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) (p+k) (p+(l+a))))
    id (gammaPreparedIndexAssoc p l a)).comp (Section5.nativeAttachSelectedVFKeys Y (Fin.castAdd k))

theorem gammaPreparedIndexAttachment_value
    (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+a))) (q : Y) :
    (gammaPreparedIndexAttachment Y q).val =
      (q.val.1,Fin.append (Fin.append (Section2.tupleRV M (q.val.1 ∘ Fin.castAdd k))
        (q.val.2 ∘ Fin.castAdd a)) (q.val.2 ∘ Fin.natAdd l)) := by
  refine Prod.ext rfl ?_
  change Fin.append (Section2.tupleRV M (q.val.1 ∘ Fin.castAdd k)) q.val.2 ∘ gammaPreparedIndexAssoc p l a = _
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [Function.comp_apply,gammaPreparedIndexAssoc,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  · intro j
    simp only [Function.comp_apply,gammaPreparedIndexAssoc,Fin.addCases_right,Fin.append_right]

theorem gammaPreparedIndexAttachment_injective
    (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+a))) :
    Function.Injective (gammaPreparedIndexAttachment Y) := by
  intro q r h
  apply Section5.nativeAttachSelectedVFKeys_injective Y (Fin.castAdd k)
  exact Section5.nativeMixedCoordinateMap_injective _ id (gammaPreparedIndexAssoc p l a)
    Function.surjective_id (gammaPreparedIndexAssoc_surjective p l a) h

def gammaPreparedIndexAttachmentBijection
    (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+a))) :
    GammaGroundBijection Y (gammaPreparedIndexAttachment Y).image :=
  ⟨(gammaPreparedIndexAttachment Y).toImage,
    (gammaPreparedIndexAttachment Y).toImage_bijective (gammaPreparedIndexAttachment_injective Y)⟩

end DiamondIntegral.Section3
