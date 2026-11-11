import «section 2».RawMapImages
import Section3.GammaRVSeparation

/-! Universal comparisons with all members of a definable real fibre.
This is the formula construction needed for uniform Gamma suprema. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n : ℕ}

def rawFibreForallCompare (G : Set (Fin n ⊕ Fin 1 → M)) (R : M → M → Prop) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∀ y : M, Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => y) ∈ G → R y (z (.inr 0))}

theorem rawFibreForallCompare_definable (S : Set M) (G : Set (Fin n ⊕ Fin 1 → M))
    (hG : S.Definable LRV G) (R : M → M → Prop)
    (hR : S.Definable₂ LRV {p | R p.1 p.2}) : S.Definable LRV (rawFibreForallCompare G R) := by
  let idx : Fin n ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr 0)
  have hLeft := hG.preimage_comp idx
  have hRight := SpecialTransformations.ModelTheory.definable_binary_at hR
    (Sum.inr (0 : Fin 1) : (Fin n ⊕ Fin 1) ⊕ Fin 1) (Sum.inl (Sum.inr (0 : Fin 1)))
  apply SpecialTransformations.ModelTheory.definable_forall_one
  convert hLeft.compl.union hRight using 1
  ext z
  have hin : z ∘ idx = Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl)
      (fun _ : Fin 1 => z (.inr 0)) := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => fin_cases j; rfl
  change (Sum.elim ((z ∘ Sum.inl) ∘ Sum.inl) (fun _ : Fin 1 => z (.inr 0)) ∈ G →
    R (z (.inr 0)) (z (.inl (.inr 0)))) ↔ (z ∘ idx ∉ G ∨ R (z (.inr 0)) (z (.inl (.inr 0))))
  rw [hin]
  exact imp_iff_not_or

end DiamondIntegral.Section2
