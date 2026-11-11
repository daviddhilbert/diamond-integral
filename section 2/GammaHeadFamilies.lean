import «section 2».GammaFamilyProjections

/-! The first-coordinate projection and its scalar indexing convention
for the induction in 2.41. The remaining coordinates are quantified. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawHeadDomain (D : Set (Fin (n+1) → M)) : Set M := {t | ∃ x ∈ D, x 0 = t}

theorem rawHeadDomain_projection (D : Set (Fin (n+1) → M)) :
    (fun x => x ∘ (fun _ : Fin 1 => (0 : Fin (n+1)))) '' D =
      {y : Fin 1 → M | y 0 ∈ rawHeadDomain D} := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,congrFun hxy 0⟩
  · rintro ⟨x,hx,hxy⟩
    refine ⟨x,hx,?_⟩
    funext j
    fin_cases j
    exact hxy

theorem rawHeadDomain_definable (S : Set M) (D : Set (Fin (n+1) → M)) (hD : S.Definable LRV D) :
    S.Definable₁ LRV (rawHeadDomain D) := by
  change S.Definable LRV {y : Fin 1 → M | y 0 ∈ rawHeadDomain D}
  rw [← rawHeadDomain_projection]
  exact hD.image_comp (fun _ : Fin 1 => (0 : Fin (n+1)))

theorem unaryGammaFamilyGraph_scalar_definable (S : Set M) (E : Set M)
    (g : (Fin 1 → M) → Gamma M)
    (hg : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ E} (fun x => {g x}))) :
    S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ E}
      (fun x => {g (fun _ : Fin 1 => x 0)})) := by
  convert hg using 1
  ext z
  have hin : (fun _ : Fin 1 => (z ∘ Sum.inl) 0) = z ∘ Sum.inl := by
    funext j
    fin_cases j
    rfl
  change (_ ∧ _ ∧ _ ∈ ({g (fun _ : Fin 1 => (z ∘ Sum.inl) 0)} : Set (Gamma M))) ↔
    (_ ∧ _ ∧ _ ∈ ({g (z ∘ Sum.inl)} : Set (Gamma M)))
  rw [hin]

end DiamondIntegral.Section2
