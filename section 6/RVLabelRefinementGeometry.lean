import «section 6».RefinedComponentImageFibres

/-! Fiber refinements are preserved by regularization and composition.
They also preserve RV-pullback membership, the terminal condition in
the lower-dimensional preparation transport. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ} {S : Set M}

def regularizedLabelSelection (n : ℕ) (π : Fin r → Fin s) : Fin (n+r) → Fin (n+s) :=
  Fin.addCases (Fin.castAdd s) (fun i => Fin.natAdd n (π i))

theorem regularizedLabelSelection_old (π : Fin r → Fin s) (v : Fin (n+s) → RVInfinity M) :
    (v ∘ regularizedLabelSelection n π) ∘ Fin.natAdd n = (v ∘ Fin.natAdd n) ∘ π := by
  funext i
  simp only [regularizedLabelSelection,Function.comp_apply,Fin.addCases_right]

theorem regularizedLabelSelection_new (π : Fin r → Fin s) (v : Fin (n+s) → RVInfinity M) :
    (v ∘ regularizedLabelSelection n π) ∘ Fin.castAdd r = v ∘ Fin.castAdd s := by
  funext i
  simp only [regularizedLabelSelection,Function.comp_apply,Fin.addCases_left]

theorem labelRefinement_regularization
    (A : DefSet (rawMixedSpace (M := M) n r) S) (C : DefSet (rawMixedSpace (M := M) n s) S)
    (π : Fin r → Fin s)
    (hFibres : ∀ u : Fin s → RVInfinity M,
      vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π))
    (v : Fin (n+s) → RVInfinity M) :
    vfFibre (regularizeMap C).image.carrier v = ∅ ∨
      vfFibre (regularizeMap C).image.carrier v =
        vfFibre (regularizeMap A).image.carrier (v ∘ regularizedLabelSelection n π) := by
  cases hFibres (v ∘ Fin.natAdd n) with
  | inl he =>
    left
    rw [regularization_carrier,regularized_fibre,he,Set.empty_inter]
  | inr he =>
    right
    simp only [regularization_carrier,regularized_fibre,he,
      regularizedLabelSelection_old,regularizedLabelSelection_new]

theorem labelRefinement_compose
    (A : Set (Mixed M n r)) (B : Set (Mixed M n s)) (C : Set (Mixed M n t))
    (π : Fin r → Fin s) (θ : Fin s → Fin t)
    (hBA : ∀ u : Fin s → RVInfinity M, vfFibre B u = ∅ ∨ vfFibre B u = vfFibre A (u ∘ π))
    (hCB : ∀ u : Fin t → RVInfinity M, vfFibre C u = ∅ ∨ vfFibre C u = vfFibre B (u ∘ θ))
    (u : Fin t → RVInfinity M) :
    vfFibre C u = ∅ ∨ vfFibre C u = vfFibre A (u ∘ (θ ∘ π)) := by
  cases hCB u with
  | inl he => exact Or.inl he
  | inr he =>
    cases hBA (u ∘ θ) with
    | inl hb => exact Or.inl (he.trans hb)
    | inr hb => exact Or.inr (he.trans hb)

theorem labelRefinement_tagged
    (A : DefSet (rawMixedSpace (M := M) n r) S) (C : DefSet (rawMixedSpace (M := M) n s) S)
    (π : Fin r → Fin s)
    (hFibres : ∀ u : Fin s → RVInfinity M,
      vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π))
    (hA : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq htags
  exact hA (p.1,p.2 ∘ π) (labelRefinement_source_subset π hFibres p hp)
    (q.1,q.2 ∘ π) (labelRefinement_source_subset π hFibres q hq) (congrArg (fun u => u ∘ π) htags)

theorem labelRefinement_pullback
    (A : DefSet (rawMixedSpace (M := M) n r) S) (C : DefSet (rawMixedSpace (M := M) n s) S)
    (π : Fin r → Fin s)
    (hFibres : ∀ u : Fin s → RVInfinity M,
      vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π))
    (hA : IsRVPullback A.carrier) : IsRVPullback C.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q,hq,hrv,htags⟩ := (mem_rvHull_iff _ p).mp hp
    have hq' : q.1 ∈ vfFibre C.carrier p.2 := htags ▸ hq
    cases hFibres p.2 with
    | inl he => rw [he] at hq'; exact hq'.elim
    | inr he =>
      have hqA : (q.1,p.2 ∘ π) ∈ A.carrier := (Set.ext_iff.mp he q.1).mp hq'
      have hpA : (p.1,p.2 ∘ π) ∈ rvHull A.carrier :=
        (mem_rvHull_iff _ _).mpr ⟨(q.1,p.2 ∘ π),hqA,hrv,rfl⟩
      rw [hA] at hpA
      exact (Set.ext_iff.mp he p.1).mpr hpA
  · exact subset_rvHull _

end DiamondIntegral.Section6
