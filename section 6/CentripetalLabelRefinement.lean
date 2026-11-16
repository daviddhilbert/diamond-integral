import «section 6».RVLabelSelection

/-! Port permitted component data to a refinement by existing RV
labels. Each new fiber is an old fiber or empty; the old focus and
coefficient are retained and all radius names stay over the new labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {C : DefSet (rawMixedSpace (M := M) n s) S}

theorem labelRefinement_source_subset (π : Fin r → Fin s)
    (hFibres : ∀ u : Fin s → RVInfinity M,
      vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π)) :
    ∀ p ∈ C.carrier, (p.1,p.2 ∘ π) ∈ A.carrier := by
  intro p hp
  cases hFibres p.2 with
  | inl h => exact False.elim (by change p.1 ∈ vfFibre C.carrier p.2 at hp; rw [h] at hp; exact hp)
  | inr h => exact (Set.ext_iff.mp h p.1).mp hp

def refinedFocusProjection (U : DefSet (rawRVSpace (M := M) r) S) (π : Fin r → Fin s)
    (hsub : ∀ p ∈ C.carrier, (p.1,p.2 ∘ π) ∈ A.carrier) :
    Map (focusActive C (selectedRVTagSet U π)) (focusActive A U) :=
  (selectRVLabelsMap (focusActive C (selectedRVTagSet U π)) π).corestrict
    (fun p => ⟨hsub p.val p.property.1,p.property.2⟩)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

def refineLabels (D : CentripetalData (G := G) A) (π : Fin r → Fin s)
    (hC : ProperInvariant S C.carrier) (hDouble : VFDoublyBounded C.carrier)
    (hTagged : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hFibres : ∀ u : Fin s → RVInfinity M,
      vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π)) :
    CentripetalData (G := G) C where
  coordinate := D.coordinate
  activeTags := selectedRVTagSet D.activeTags π
  focus x u := D.focus x (u ∘ π)
  focusMap := D.focusMap.comp (refinedFocusProjection D.activeTags π (labelRefinement_source_subset π hFibres))
  focusMap_eq := by
    intro p
    exact D.focusMap_eq (refinedFocusProjection D.activeTags π (labelRefinement_source_subset π hFibres) p)
  sourceProper := hC
  sourceDoublyBounded := hDouble
  tagged := hTagged
  continuous := by
    intro u hu
    cases hFibres u with
    | inl he => rw [he]; exact continuousOn_empty _
    | inr he => rw [he]; exact D.continuous (u ∘ π) hu
  focusRV := by
    intro p hp hu
    exact D.focusRV (p.1,p.2 ∘ π) (labelRefinement_source_subset π hFibres p hp) hu
  coefficient := D.coefficient
  coefficient_nonzero := D.coefficient_nonzero
  coefficient_nonnegative := D.coefficient_nonnegative
  coefficient_definable := D.coefficient_definable
  covariance := by
    intro u hu
    obtain ⟨α,β,hα,hβ,hInv,hCov,hDom⟩ := D.covariance (u ∘ π) hu
    refine ⟨α,β,hα.mono (selectedRVLabels_base_subset π u),
      fun i => (hβ i).mono (selectedRVLabels_base_subset π u),?_,?_,?_⟩
    · cases hFibres u with
      | inl he => rw [he]; exact fun _ _ _ => Iff.rfl
      | inr he => rw [he]; exact hInv
    · intro a ha b hb hab
      exact hCov a (labelRefinement_source_subset π hFibres (a,u) ha)
        b (labelRefinement_source_subset π hFibres (b,u) hb) hab
    · intro a ha
      exact hDom a (labelRefinement_source_subset π hFibres (a,u) ha)

end CentripetalData
end DiamondIntegral.Section6
