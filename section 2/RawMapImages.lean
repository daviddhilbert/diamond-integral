import «section 2».RVMapGraphs
import Section3.DefinableConstants

/-! Existential images of definable raw maps over the same real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem raw_definable_map_image (S : Set M) (D : Set (Fin n → M))
    (hD : S.Definable LRV D) (F : (Fin n → M) → Fin m → M)
    (hF : S.DefinableMap LRV F) : S.Definable LRV (F '' D) := by
  have hG := rvRawMapGraph_definable S D hD F hF
  convert hG.image_comp (fun j => finSumFinEquiv (.inr j)) using 1
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    let w : Fin (n+m) → M := Sum.elim x (F x) ∘ finSumFinEquiv.symm
    have hin : w ∘ finSumFinEquiv ∘ Sum.inl = x := by
      funext j
      simp only [w,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    have hout : w ∘ finSumFinEquiv ∘ Sum.inr = F x := by
      funext j
      simp only [w,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    exact ⟨w,⟨hin.symm ▸ hx,by rw [hin,hout]⟩,hout⟩
  · rintro ⟨w,⟨hx,hF⟩,hw⟩
    exact ⟨w ∘ finSumFinEquiv ∘ Sum.inl,hx,hF.trans hw⟩

def rawRVValues (x : Fin n → M) : Fin n → M := iRv ∘ x

theorem rawRVValues_definable (S : Set M) : S.DefinableMap LRV (rawRVValues (M := M) (n := n)) := by
  intro j
  exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
    (show S.DefinableMap LRV (fun x : Fin n → M => ![x j]) from by
      intro k
      fin_cases k
      exact Set.DefinableFun.proj LRV)

end DiamondIntegral.Section2
