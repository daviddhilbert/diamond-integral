import «section 2».RVMapRestriction

/-! A definable RV set finite over m existing coordinate tags has an
actual finite-to-one map to RV^m, including zero tags in those coordinates. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

theorem finite_function_fibres_comp {α β γ : Type*} (f : α → β) (g : β → γ)
    (hf : ∀ b, {a | f a = b}.Finite) (hg : ∀ c, {b | g b = c}.Finite) (c : γ) :
    {a | g (f a) = c}.Finite := by
  have h : (⋃ b ∈ {b | g b = c}, {a | f a = b}).Finite :=
    (hg c).biUnion (fun b _ => hf b)
  apply h.subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨f a,Set.mem_iUnion.mpr ⟨ha,rfl⟩⟩

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_finite_map_of_finite_projection (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n m : ℕ} (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) (π : Fin m → Fin n)
    (hfinite : ∀ t : Fin m → RVInfinity M, {u : U | u.val ∘ π = t}.Finite) :
    RVHasFiniteMap S U m := by
  let p (u : U) := u.val ∘ π
  let g (u : U) := rvCollapseTuple (p u)
  refine ⟨g,finite_function_fibres_comp p rvCollapseTuple hfinite rvCollapseTuple_finite_fibres,?_⟩
  let F (z : Fin n → M) (i : Fin m) := nonzeroRVCode (z (π i)) 0
  have hF : S.DefinableMap LRV F := fun i => nonzeroRVCode_definable S (π i) 0
  exact rvMapGraph_definable_of_raw_map hc S U hU g F hF (fun _ => rfl)

theorem rvDimension_lt_of_finite_projection (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n m : ℕ} (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) (π : Fin m → Fin n)
    (hfinite : ∀ t : Fin m → RVInfinity M, {u : U | u.val ∘ π = t}.Finite) (hm : m < n) :
    rvDimension S U < (n : WithBot ℕ) :=
  lt_of_le_of_lt (rvDimension_le_of_finite_map
    (rv_finite_map_of_finite_projection hc S U hU π hfinite)) (by exact_mod_cast hm)

end DiamondIntegral.Section2
