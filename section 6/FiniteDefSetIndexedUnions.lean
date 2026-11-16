import «section 6».FiniteDefSetUnions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M} {P : Space LRV M} {I : Type} [DecidableEq I]

def finiteDefSetIndexedUnion (D : I → DefSet P S) (J : Finset I) : DefSet P S :=
  finiteDefSetUnion (fun j : {j // j ∈ J} => D j.val)

theorem finiteDefSetIndexedUnion_mem (D : I → DefSet P S) (J : Finset I) (x : P.Carrier) :
    x ∈ (finiteDefSetIndexedUnion D J).carrier ↔ ∃ j ∈ J, x ∈ (D j).carrier := by
  change (x ∈ ⋃ j : {j // j ∈ J}, (D j.val).carrier) ↔ _
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j.val,j.property,hj⟩
  · rintro ⟨j,hj,hx⟩
    exact ⟨⟨j,hj⟩,hx⟩

theorem finiteDefSetIndexedUnion_subset (D : I → DefSet P S) (J : Finset I) (A : DefSet P S)
    (hD : ∀ j, (D j).carrier ⊆ A.carrier) : (finiteDefSetIndexedUnion D J).carrier ⊆ A.carrier := by
  intro x hx
  obtain ⟨j,hj,hx⟩ := (finiteDefSetIndexedUnion_mem D J x).mp hx
  exact hD j hx

theorem finiteDefSetIndexedUnion_empty (D : I → DefSet P S) (x : P.Carrier) :
    x ∉ (finiteDefSetIndexedUnion D ∅).carrier := by
  rw [finiteDefSetIndexedUnion_mem]
  simp only [Finset.notMem_empty,false_and,exists_false,not_false_eq_true]

theorem finiteDefSetIndexedUnion_insert (D : I → DefSet P S) (J : Finset I) (i : I) (x : P.Carrier) :
    x ∈ (finiteDefSetIndexedUnion D (insert i J)).carrier ↔
      x ∈ (finiteDefSetIndexedUnion D J).carrier ∨ x ∈ (D i).carrier := by
  rw [finiteDefSetIndexedUnion_mem,finiteDefSetIndexedUnion_mem]
  simp only [Finset.mem_insert]
  constructor
  · rintro ⟨j,hj,hx⟩
    rcases hj with rfl | hj
    · exact Or.inr hx
    · exact Or.inl ⟨j,hj,hx⟩
  · rintro (⟨j,hj,hx⟩ | hx)
    · exact ⟨j,Or.inr hj,hx⟩
    · exact ⟨i,Or.inl rfl,hx⟩

end DiamondIntegral.Section6
