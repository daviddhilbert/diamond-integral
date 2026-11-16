import «section 6».CarriedCentripetalMaps

/-! Actual original-base coordinate selection on retained RV labels.
Every VF coordinate stays fixed; a selected old label is an existing
coordinate of the new tuple, so its parameter names need no enlargement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}

def selectRVLabelsMap (C : DefSet (rawMixedSpace (M := M) n s) S) (π : Fin r → Fin s) :
    Map C (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) n s
  let Q := rawMixedSpace (M := M) n r
  let F (p : Mixed M n s) : Mixed M n r := (p.1,p.2 ∘ π)
  let codes (z : Fin n ⊕ Fin s → M) : Fin n ⊕ Fin r → M :=
    Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (π i)))
  have hcodes : S.DefinableMap LRV codes := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (F (P.decode z)) = codes z.val := by
    have he := mixedValues_decode z
    funext i
    cases i with
    | inl i => exact congrFun he (.inl i)
    | inr i => exact congrFun he (.inr (π i))
  have hdom (z : P.domain) : codes z.val ∈ Q.domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes C F codes hcodes hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨_,hdom z⟩).trans (hcode z).symm))

theorem selectedRVLabels_base_subset (π : Fin r → Fin s) (u : Fin s → RVInfinity M) :
    S ∪ Set.range (rvValues (u ∘ π)) ⊆ S ∪ Set.range (rvValues u) := by
  rintro x (hx | ⟨i,rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨π i,rfl⟩

theorem rvValues_preimage_definable (R : Set (Fin r → M)) (hR : S.Definable LRV R) :
    (rawRVSpace (M := M) r).Definable S {u | rvValues u ∈ R} := by
  let P := rawRVSpace (M := M) r
  change S.Definable LRV (P.preimage {u | rvValues u ∈ R})
  convert (P.definable_domain S).inter hR using 1
  ext z
  constructor
  · rintro ⟨hz,hzR⟩
    change rvValues (P.decode ⟨z,hz⟩) ∈ R at hzR
    have he : rvValues (P.decode ⟨z,hz⟩) = z := rvValues_decode ⟨z,hz⟩
    exact ⟨hz,he ▸ hzR⟩
  · rintro ⟨hz,hzR⟩
    refine ⟨hz,?_⟩
    change rvValues (P.decode ⟨z,hz⟩) ∈ R
    have he : rvValues (P.decode ⟨z,hz⟩) = z := rvValues_decode ⟨z,hz⟩
    exact he.symm ▸ hzR

def selectedRVTagSet (U : DefSet (rawRVSpace (M := M) r) S) (π : Fin r → Fin s) :
    DefSet (rawRVSpace (M := M) s) S := by
  let R : Set (Fin s → M) := {z | z ∘ π ∈ (rawRVSpace r).preimage U.carrier}
  have hR : S.Definable LRV R := U.definable.preimage_comp π
  refine ⟨{u | u ∘ π ∈ U.carrier},?_⟩
  convert rvValues_preimage_definable R hR using 1
  ext u
  change u ∘ π ∈ U.carrier ↔ rvValues (u ∘ π) ∈ (rawRVSpace r).preimage U.carrier
  constructor
  · intro hu
    exact ⟨⟨u ∘ π,rfl⟩,by simpa only [decode_rvValues] using hu⟩
  · rintro ⟨hz,hu⟩
    simpa only [decode_rvValues] using hu

end DiamondIntegral.Section6
