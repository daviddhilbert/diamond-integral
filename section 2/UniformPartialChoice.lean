import «section 2».FinitePartialChoice

/-! Compactness for a family of definable partial unique choices. The
pointwise witness is an original-base definable subrelation, not a new
model parameter or a global choice assumption. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n : ℕ}

theorem uniform_partial_unique_choice {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (J : Set (Fin n → M))
    (hJ : S.Definable LRV J) (T : (Fin n → M) → Set M)
    (hpartial : ∀ p ∈ J, ∃ R : (Fin n → M) → Set M,
      S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)} ∧
      (∀ q ∈ J, R q ⊆ T q) ∧ p ∈ rawSingletonRows R) :
    ∃ f : (Fin n → M) → M,
      S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z ∘ Sum.inl ∈ J ∧ f (z ∘ Sum.inl) = z (.inr 0)} ∧
      ∀ p ∈ J, f p ∈ T p := by
  classical
  let C : Set (Set (Fin n → M)) := {D | ∃ R : (Fin n → M) → Set M,
    S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)} ∧
    (∀ q ∈ J, R q ⊆ T q) ∧ D = J ∩ rawSingletonRows R}
  have hC : ∀ D ∈ C, S.Definable LRV D := by
    rintro D ⟨R,hR,_,rfl⟩
    exact hJ.inter (rawSingletonRows_definable S R hR)
  have hcover : ∀ p ∈ J, ∃ D ∈ C, p ∈ D := by
    intro p hp
    obtain ⟨R,hR,hRT,hpR⟩ := hpartial p hp
    exact ⟨J ∩ rawSingletonRows R,⟨R,hR,hRT,rfl⟩,hp,hpR⟩
  obtain ⟨C₀,hCf,hCsub,hCcov⟩ := hs.definable_finite_subcover_tuple S hsmall J hJ C hC hcover
  haveI : Finite C₀ := hCf.to_subtype
  letI := Fintype.ofFinite C₀
  let e : Fin (Fintype.card C₀) ≃ C₀ := (Fintype.equivFin C₀).symm
  let P (D : C₀) : (Fin n → M) → Set M := Classical.choose (hCsub D.property)
  have hP (D : C₀) : S.Definable LRV
      {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ P D (z ∘ Sum.inl)} :=
    (Classical.choose_spec (hCsub D.property)).1
  have hPT (D : C₀) : ∀ q ∈ J, P D q ⊆ T q :=
    (Classical.choose_spec (hCsub D.property)).2.1
  have hPD (D : C₀) : D.val = J ∩ rawSingletonRows (P D) :=
    (Classical.choose_spec (hCsub D.property)).2.2
  have hcov : ∀ p ∈ J, ∃ i : Fin (Fintype.card C₀), p ∈ rawSingletonRows (P (e i)) := by
    intro p hp
    obtain ⟨D,hDC,hpD⟩ := hCcov p hp
    let d : C₀ := ⟨D,hDC⟩
    have hpP : p ∈ rawSingletonRows (P d) := by
      have hp' : p ∈ J ∩ rawSingletonRows (P d) := by
        rw [← hPD d]
        exact hpD
      exact hp'.2
    refine ⟨e.symm d,?_⟩
    simpa only [e.apply_symm_apply] using hpP
  exact finite_partial_unique_choice S J hJ (fun i => P (e i)) (fun i => hP (e i)) hcov T
    (fun i => hPT (e i))

end DiamondIntegral.Section2
