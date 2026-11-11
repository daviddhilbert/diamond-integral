import «section 2».Conventions
import Section3.FieldBase
import Section3.AclModelGeometry
import Section3.VFDefinableClosure

/-!
# Field-generated bases for Lemma 2.11

Substructure generation is kept separate from definable closure. The standing
field convention and surjectivity of rv are explicit, including rv(0).
No definable-closedness or henselianity is part of this base interface.
-/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Generation in the language, rather than generation under dcl. -/
def VFGenerated (S : LRV.Substructure M) : Prop :=
  ∃ A : Set M, (∀ a ∈ A, iVF a) ∧ Substructure.closure LRV A = S

/-- The VF field and the RV representatives of the paper's base.
The field requirement is the manuscript's standing substructure convention. -/
structure VFGeneratedFieldBase (S : LRV.Substructure M) extends VFFieldBase (S : Set M) where
  rv_lift : ∀ t ∈ S, iRV t → ∃ a : field, iRv a.val.val = t

variable {S : LRV.Substructure M} (B : VFGeneratedFieldBase S)

theorem VFGeneratedFieldBase.fieldNames_subset : vfFieldNames B.field ⊆ (S : Set M) := by
  rintro _ ⟨a, ha, rfl⟩
  exact (B.mem_iff a).mp ha

include B in
theorem VFGeneratedFieldBase.vfGenerated : VFGenerated S := by
  refine ⟨vfFieldNames B.field, ?_, ?_⟩
  · rintro _ ⟨a, _, rfl⟩
    exact a.property
  · apply le_antisymm
    · exact Substructure.closure_le.mpr B.fieldNames_subset
    · intro x hx
      rcases TypedModelMap.sort_cover (M := M) x with hVF | hRV
      · exact Substructure.subset_closure ⟨⟨x, hVF⟩, (B.mem_iff _).mpr hx, rfl⟩
      · obtain ⟨a, ha⟩ := B.rv_lift x hx hRV
        rw [← ha]
        exact (Substructure.closure LRV (vfFieldNames B.field)).fun_mem Fn.rvMap
          ![a.val.val] (by
            intro i
            fin_cases i
            exact Substructure.subset_closure ⟨a.val, a.property, rfl⟩)

theorem VFGeneratedFieldBase.definable_over_fieldNames (x : M) (hx : x ∈ S) :
    ∃ σ, DefinableClosureAt (vfFieldNames B.field) σ x := by
  rcases TypedModelMap.sort_cover (M := M) x with hVF | hRV
  · exact ⟨.vf, definableClosureAt_of_mem
      ⟨⟨x, hVF⟩, (B.mem_iff _).mpr hx, rfl⟩ hVF⟩
  · obtain ⟨a, ha⟩ := B.rv_lift x hx hRV
    exact ⟨.rv, ha ▸ rv_definable_over_field_names B.field a⟩

/-- Forgetting the redundant RV names does not change definable closure. -/
theorem VFGeneratedFieldBase.definableClosure_fieldNames :
    definableClosure (vfFieldNames B.field) = definableClosure (S : Set M) := by
  apply Set.Subset.antisymm
  · rintro x ⟨σ, hx⟩
    exact ⟨σ, hx.mono B.fieldNames_subset⟩
  · rintro x ⟨σ, hx⟩
    exact ⟨σ, hx.eliminate_sorted_definable_params B.definable_over_fieldNames⟩

/-- The field-theoretic algebraic closure in Lemma 2.11 uses precisely VF(S). -/
theorem VFGeneratedFieldBase.algebraicAt_vf_iff (a : VF M) :
    AlgebraicAt (S : Set M) .vf a.val ↔ IsAlgebraic B.field a :=
  B.toVFFieldBase.algebraicAt_iff (S : Set M) a

end DiamondIntegral.Section2
