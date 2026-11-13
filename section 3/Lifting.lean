import «section 3».RVCategories
import «section 3».VFCategories
import Section4.CanonicalLift

/-! Notation 3.21 (`RVcat:tag`): the object lift preserves the full RV label.
Its finite-fibre property is unconditional; descent along isomorphism
classes is a separate result requiring the base-generation hypothesis. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

noncomputable def objectLift (U : RVObject (M := M) S k) :
    DefSet (rawMixedSpace (M := M) k U.arity) S := rvLift U.toCompanion.obj

theorem mem_objectLift (U : RVObject (M := M) S k)
    (p : Section2.Mixed M k U.arity) : p ∈ (objectLift U).carrier ↔
      ∃ u : U.domain, u.val = p.2 ∧ (U.volume u).val = Section2.tupleRV M p.1 := Iff.rfl

theorem objectLift_finite_rv_fibres (U : RVObject (M := M) S k)
    (a : Fin k → Section2.VF M) :
    {t | (a, t) ∈ (objectLift U).carrier}.Finite :=
  rvLift_finite_rv_fibres U.toCompanion.obj U.finite a

/-- The object lift lands in VF[k] for the section 2 dimension convention.
No lift of a morphism or representative choice is used in this construction. -/
noncomputable def objectLiftVF [TopologicalSpace (Section2.VF M)]
    (U : RVObject (M := M) S k) : VFObject S k :=
  vfObjectOfFiniteFibres (objectLift U) (objectLift_finite_rv_fibres U)

theorem objectLift_vf_coordinates_nonzero (U : RVObject (M := M) S k)
    (p : Section2.Mixed M k U.arity) (hp : p ∈ (objectLift U).carrier) (i : Fin k) :
    p.1 i ≠ 0 := by
  obtain ⟨u, _, hu⟩ := (mem_objectLift U p).mp hp
  intro hz
  have hrv := congrArg (fun t => (t i).val) hu
  have hzero : (Section2.tupleRV M p.1 i).val = iRVZero := by
    rw [Section2.tupleRV, hz, Section2.rv_zero]
    rfl
  exact U.nonzero u i (hrv.trans hzero)

end DiamondIntegral.Section3
