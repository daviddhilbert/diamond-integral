import «section 2».RVDimension
import Section3.GammaBaseTools

/-! Full graphs of original-base RV maps built from definable raw maps.
Inputs retain RV-infinity coordinates; targets have only nonzero RV entries. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m k : ℕ}

theorem rvInputValues_injective : Function.Injective (rvInputValues (M := M) (m := m)) := by
  intro u v he
  funext i
  exact Subtype.ext (congrFun he i)

def rvRawMapGraph (V : Set (Fin m → M)) (F : (Fin m → M) → Fin k → M) :
    Set (Fin (m+k) → M) :=
  {z | z ∘ finSumFinEquiv ∘ Sum.inl ∈ V ∧
    F (z ∘ finSumFinEquiv ∘ Sum.inl) = z ∘ finSumFinEquiv ∘ Sum.inr}

theorem rvRawMapGraph_definable (S : Set M) (V : Set (Fin m → M))
    (hV : S.Definable LRV V) (F : (Fin m → M) → Fin k → M)
    (hF : S.DefinableMap LRV F) : S.Definable LRV (rvRawMapGraph V F) := by
  have hg : S.Definable LRV {z : Fin (m+k) → M |
      F (z ∘ finSumFinEquiv ∘ Sum.inl) = z ∘ finSumFinEquiv ∘ Sum.inr} := by
    have h (j : Fin k) := (hF j).preimage_comp
      (fun i : Option (Fin m) => i.elim (finSumFinEquiv (.inr j))
        (fun l => finSumFinEquiv (.inl l)))
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_preimage,Function.tupleGraph]
    exact ⟨fun he j => congrFun he j,fun he => funext he⟩
  exact (hV.preimage_comp (fun j => finSumFinEquiv (.inl j))).inter hg

theorem rvMapGraph_of_raw_map
    (U : Set (Fin m → RVInfinity M)) (f : U → Fin k → RV M)
    (F : (Fin m → M) → Fin k → M)
    (hf : ∀ u, rvTargetValues (f u) = F (rvInputValues u.val)) :
    rvMapGraph U f = rvRawMapGraph (rvInputValues '' U) F := by
  ext z
  constructor
  · rintro ⟨u,hu,he⟩
    refine ⟨⟨u.val,u.property,hu⟩,?_⟩
    change F (z ∘ finSumFinEquiv ∘ Sum.inl) = _
    rw [← hu,← hf]
    exact he
  · rintro ⟨⟨u,hu,he⟩,hF⟩
    refine ⟨⟨u,hu⟩,he,?_⟩
    rw [hf,he]
    exact hF

theorem rvMapGraph_sorted (U : Set (Fin m → RVInfinity M)) (f : U → Fin k → RV M) :
    rvMapGraph U f ⊆ GammaParameters.sortedUniverse (fun _ => .rv) := by
  rintro z ⟨u,hx,hy⟩ i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    change iRV (z (finSumFinEquiv (.inl j)))
    have he := congrFun hx j
    change (u.val j).val = z (finSumFinEquiv (.inl j)) at he
    rw [← he]
    exact (u.val j).property
  | inr j =>
    change iRV (z (finSumFinEquiv (.inr j)))
    have he := congrFun hy j
    change (f u j).val.val = z (finSumFinEquiv (.inr j)) at he
    rw [← he]
    exact (f u j).val.property

theorem rvMapGraph_definable_of_raw_map
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M)
    (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U))
    (f : U → Fin k → RV M) (F : (Fin m → M) → Fin k → M)
    (hF : S.DefinableMap LRV F)
    (hf : ∀ u, rvTargetValues (f u) = F (rvInputValues u.val)) :
    DefinableOver S (fun _ => .rv) (rvMapGraph U f) := by
  apply raw_definableOver_sorted hc
  · rw [rvMapGraph_of_raw_map U f F hf]
    exact rvRawMapGraph_definable S _ hU.raw_definable F hF
  · exact rvMapGraph_sorted U f

end DiamondIntegral.Section2
