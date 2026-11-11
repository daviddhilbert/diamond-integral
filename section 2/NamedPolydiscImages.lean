import «section 2».NamedCoordinateMaps
import «section 2».CitedDiscRVImages
import «section 2».PolydiscImages

/-! The coordinate-chain image argument in 2.29 with existing DC names.
Only geometric C-minimality uses an auxiliary presentation base; image
atomicity and every unary line use the original retained disc names. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem atomic_open_polydisc_image_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (f : (Fin n → M) → M)
    (hG : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      (vfFunctionGraph {a | ∀ j, a j ∈ D j} f))
    (hproper : {x : VF M | x.val ∈ f '' {a | ∀ j, a j ∈ D j}} ≠ Set.univ) :
    (∃ c : VF M, ∀ a ∈ {a | ∀ j, a j ∈ D j}, f a = c.val) ∨
      (IsAtomicOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .vf)
        {z | z 0 ∈ f '' {a | ∀ j, a j ∈ D j}} ∧ IsOpenDisc (f '' {a | ∀ j, a j ∈ D j})) := by
  have hI := vf_function_image_atomic_disc_names B ground d τ _ f hA hG
  by_cases hconst : ∃ c : M, ∀ a ∈ {a | ∀ j, a j ∈ D j}, f a = c
  · obtain ⟨c,hcval⟩ := hconst
    obtain ⟨a,ha⟩ := hA.2.1
    have hcVF : iVF c := by
      have hm : (fun _ : Fin 1 => c) ∈ {z | z 0 ∈ f '' {a | ∀ j, a j ∈ D j}} := ⟨a,ha,hcval a ha⟩
      simpa only [sortEval,iVF] using hI.1.proper hm (0 : Fin 1)
    exact Or.inl ⟨⟨c,hcVF⟩,hcval⟩
  · refine Or.inr ⟨hI,?_⟩
    obtain ⟨R,hRG⟩ := hG
    have hAux := R.definable_fibre d τ
    rw [hRG] at hAux
    apply rectangle_image_isOpenDisc h00 _ D f hA.2.1 hAux hproper hconst
    intro a ha
    cases n with
    | zero => intro i; exact i.elim0
    | succ n =>
      intro i
      let E := tupleBase B (Fin.removeNth i a)
      have hΓE : NontrivialDefinableGamma E := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have hline := coordinate_line_atomic_disc_names hc B ground d τ D hA a ha i
      have hgraph := coordinate_line_graph_definable_disc_names B ground d τ D f ⟨R,hRG⟩ a ha i
      exact named_open_disc_image h00 E hΓE (cited E) ground d τ _ _ hline (hopen i) hgraph

end DiamondIntegral.Section2
