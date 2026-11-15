import «section 5».OriginalRVTagDomains
import «section 5».GammaGroundDisjointBijections
import «section 4».Section3RVCodeBridge

/-! The literal raw tags agree with the actual native Gamma-ground tag
maps. Their full tagged domains have exactly the displayed raw rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {a b : ℕ}

theorem raw_native_left_tag (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (u : A) :
    rvValues ((gammaGroundRVLeftTag A b) u).val = rawRVLeftTag b (rvValues u.val) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [rvValues, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
      rvMapOfCode, Map.ofCodes, rvLeftTag, rawRVLeftTag, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [rvValues, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
        rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend, rawRVLeftTag, Fin.append_left, Fin.append_right]
    · simp only [rvValues, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
        rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend, rvZeroTuple, rawRVLeftTag, Fin.append_right]

theorem raw_native_right_tag (A : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) (u : A) :
    rvValues ((gammaGroundRVRightTag A a) u).val = rawRVRightTag a (rvValues u.val) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [rvValues, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
      rvMapOfCode, Map.ofCodes, rvRightTag, rawRVRightTag, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [rvValues, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
        rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend, rvZeroTuple, rawRVRightTag, Fin.append_left, Fin.append_right]
    · simp only [rvValues, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
        rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend, rawRVRightTag, Fin.append_right]

theorem rawDomain_native_tagged_union
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) (w : Fin (1+(a+b)) → M) :
    w ∈ rawDomain (gammaGroundRVTaggedUnion A C) ↔
      (∃ x ∈ rawDomain A, w = rawRVLeftTag b x) ∨ (∃ y ∈ rawDomain C, w = rawRVRightTag a y) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases hv with ⟨u, hu⟩ | ⟨u, hu⟩
    · refine Or.inl ⟨rvValues u.val, ⟨u.val, u.property, rfl⟩, ?_⟩
      rw [← hu]
      exact raw_native_left_tag A u
    · refine Or.inr ⟨rvValues u.val, ⟨u.val, u.property, rfl⟩, ?_⟩
      rw [← hu]
      exact raw_native_right_tag C u
  · rintro (⟨_, ⟨u, hu, rfl⟩, rfl⟩ | ⟨_, ⟨u, hu, rfl⟩, rfl⟩)
    · exact ⟨((gammaGroundRVLeftTag A b) ⟨u, hu⟩).val, Or.inl ⟨⟨u, hu⟩, rfl⟩,
        raw_native_left_tag A ⟨u, hu⟩⟩
    · exact ⟨((gammaGroundRVRightTag C a) ⟨u, hu⟩).val, Or.inr ⟨⟨u, hu⟩, rfl⟩,
        raw_native_right_tag C ⟨u, hu⟩⟩

end DiamondIntegral.Section5
