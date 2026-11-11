import «section 2».RVMapReindexing
import Section3.GammaProjection

/-! Definability of finite-map domains and dimension under coordinate
permutations, retaining exactly the original parameter set. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem RVHasFiniteMap.domain_definable {S : Set M} {m k : ℕ}
    {U : Set (Fin m → RVInfinity M)} (hU : RVHasFiniteMap S U k) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' U) := by
  obtain ⟨f,hfin,hG⟩ := hU
  have hGB := (GammaParameters.base_empty_iff S _ _).mpr hG
  have hp := (GammaParameters.base_empty_iff S _ _).mp
    (hGB.image_real (fun j => finSumFinEquiv (.inl j)))
  change DefinableOver S (fun _ => .rv)
    ((fun x => x ∘ fun j => finSumFinEquiv (.inl j)) '' rvMapGraph U f) at hp
  convert hp using 1
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    let w : Fin (m+k) → M :=
      Sum.elim (rvInputValues u) (rvTargetValues (f ⟨u,hu⟩)) ∘ finSumFinEquiv.symm
    have hin : w ∘ finSumFinEquiv ∘ Sum.inl = rvInputValues u := by
      funext j
      simp only [w,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    have hout : w ∘ finSumFinEquiv ∘ Sum.inr = rvTargetValues (f ⟨u,hu⟩) := by
      funext j
      simp only [w,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    exact ⟨w,⟨⟨u,hu⟩,hin.symm,hout.symm⟩,hin⟩
  · rintro ⟨w,⟨u,hx,hy⟩,hw⟩
    exact ⟨u.val,u.property,hx.trans hw⟩

theorem rvReindexed_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {m n : ℕ} (e : Fin m ≃ Fin n) (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' rvReindexed e U) :=
  ((rv_finite_map_to_arity hc S U hU).reindex hc e).domain_definable

theorem rvDimension_reindex_le (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {m n : ℕ} (e : Fin m ≃ Fin n) (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    rvDimension S (rvReindexed e U) ≤ rvDimension S U := by
  classical
  by_cases hne : U.Nonempty
  · let k := sInf {l | RVHasFiniteMap S U l}
    have hk : RVHasFiniteMap S U k := by
      change sInf {l | RVHasFiniteMap S U l} ∈ {l | RVHasFiniteMap S U l}
      exact Nat.sInf_mem ⟨n,rv_finite_map_to_arity hc S U hU⟩
    have hd : rvDimension S U = (k : WithBot ℕ) := by
      simp only [rvDimension,ite_eq_left hne,k]
    rw [hd]
    exact rvDimension_le_of_finite_map (hk.reindex hc e)
  · have he : rvReindexed e U = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      rfl
    calc
      rvDimension S (rvReindexed e U) = ⊥ := by rw [he,rvDimension_empty]
      _ ≤ rvDimension S U := bot_le

end DiamondIntegral.Section2
