import «section 2».AlgebraicChoice

/-! Naming finite VF tuples preserves the pure VF algebraic-core data
used in modelhood and finite choice. No radius representatives are added. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] (v : Valuation (VF M) G)

theorem VFGeneratedFieldBase.parameter_core (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ v x.val ≠ 1) {q : ℕ} (p : Fin q → VF M) :
    let V := vfFieldNames B.field ∪ Set.range (vfValues p)
    let T : Set M := (S : Set M) ∪ Set.range (vfValues p)
    (∀ x ∈ V, iVF x) ∧ V ⊆ T ∧ T ⊆ algebraicClosureSet V ∧
      ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1 := by
  let V := vfFieldNames B.field ∪ Set.range (vfValues p)
  let T : Set M := (S : Set M) ∪ Set.range (vfValues p)
  have hV : ∀ x ∈ V, iVF x := by
    rintro x (hx | ⟨i,rfl⟩)
    · obtain ⟨a,ha,rfl⟩ := hx
      exact a.property
    · exact (p i).property
  have hVT : V ⊆ T := Set.union_subset_union B.fieldNames_subset (Set.Subset.refl _)
  have hTV : T ⊆ algebraicClosureSet V := by
    rintro x (hx | hx)
    · obtain ⟨σ,hσ⟩ := B.definable_over_fieldNames x hx
      exact ⟨σ,hσ.algebraic.mono Set.subset_union_left⟩
    · exact subset_algebraicClosureSet V (Or.inr hx)
  refine ⟨hV,hVT,hTV,?_⟩
  obtain ⟨x,hx0,hxv⟩ := hnt
  have hname : x.val.val ∈ V := Or.inl ⟨x.val,x.property,rfl⟩
  have hxV : x.val ∈ vfAlgebraicClosureField V :=
    (mem_vfAlgebraicClosureField V x.val).mpr
      (definableClosureAt_of_mem (σ := .vf) hname x.val.property).algebraic
  refine ⟨⟨x.val,hxV⟩,?_,hxv⟩
  intro he
  have heval : x.val = 0 := congrArg (fun y : vfAlgebraicClosureField V => y.val) he
  exact hx0 (Subtype.ext heval)

end DiamondIntegral.Section2
