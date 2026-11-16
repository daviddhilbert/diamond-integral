import «section 6».VFCoordinateReindexing

/-! Coordinate erasure, congruence and complete focus projections
under VF coordinate permutations. These are changes of presentation
used to conjugate actual permitted component chains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem update_comp_fin_equiv {E : Type*} (a : Fin n → E) (e : Fin n ≃ Fin n) (j : Fin n) (v : E) :
    Function.update a j v ∘ e=Function.update (a ∘ e) (e.symm j) v := by
  funext i
  by_cases hi : i=e.symm j
  · subst i
    simp only [Function.comp_apply,Equiv.apply_symm_apply,Function.update_self]
  · have hOld : e i ≠ j := by
      intro h
      exact hi (by simpa only [Equiv.symm_apply_apply] using congrArg e.symm h)
    simp only [Function.comp_apply,Function.update_of_ne hi,Function.update_of_ne hOld]

theorem erased_comp_fin_equiv {E : Type*} (a : Fin n → E) (e : Fin n ≃ Fin n) (j : Fin n) (v : E) :
    Function.update a (e.symm j) v ∘ e.symm=Function.update (a ∘ e.symm) j v := by
  simpa only [Equiv.symm_symm,Equiv.apply_symm_apply] using update_comp_fin_equiv a e.symm (e.symm j) v

theorem coordinate_radius_comp_fin_equiv (α : Gamma M) (β : Fin n → Gamma M)
    (e : Fin n ≃ Fin n) (j : Fin n) :
    (fun i => if i=j then α else β i) ∘ e=(fun i => if i=e.symm j then α else β (e i)) := by
  funext i
  by_cases hi : i=e.symm j
  · subst i
    simp only [Function.comp_apply,Equiv.apply_symm_apply,ite_true]
  · have hOld : e i ≠ j := by
      intro h
      exact hi (by simpa only [Equiv.symm_apply_apply] using congrArg e.symm h)
    simp only [Function.comp_apply,if_neg hi,if_neg hOld]

theorem congruent_comp_fin_equiv (α : Fin n → Gamma M) (e : Fin n ≃ Fin n)
    (a b : Fin n → VF M) (hab : Congruent (α ∘ e) a b) :
    Congruent α (a ∘ e.symm) (b ∘ e.symm) := by
  intro i
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hab (e.symm i)

theorem reindexedVFSet_tagged (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    ∀ p ∈ (reindexedVFSet A e).carrier,∀ q ∈ (reindexedVFSet A e).carrier,
      p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  intro p hp q hq hTags
  have h := hA _ ((mem_reindexedVFSet A e p).mp hp) _ ((mem_reindexedVFSet A e q).mp hq) hTags
  funext i
  have hAt := congrFun h (e i)
  change rv M (p.1 (e.symm (e i)))=rv M (q.1 (e.symm (e i))) at hAt
  change rv M (p.1 i)=rv M (q.1 i)
  simpa only [Equiv.symm_apply_apply] using hAt

def reindexedFocusProjection (A : DefSet (rawMixedSpace (M := M) n r) S)
    (U : DefSet (rawRVSpace (M := M) r) S) (e : Fin n ≃ Fin n) :
    Map (focusActive (reindexedVFSet A e) U) (focusActive A U) :=
  (reindexVFMap (focusActive (reindexedVFSet A e) U) e.symm).corestrict
    (fun p => ⟨(mem_reindexedVFSet A e p.val).mp p.property.1,p.property.2⟩)

end DiamondIntegral.Section6
