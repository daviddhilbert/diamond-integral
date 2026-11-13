import «section 4».FieldDefinableRing

/-! Empty and singleton pure-field charts have classes zero and one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldPointCharts
open FieldDefinableRing DefinableBiUniqueRelation
variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem objectClass_empty (a : Chart K) (ha : a.domain = ∅) : objectClass K a = 0 := by
  have hb : BiUnique (domain K (.atom a)) (domain K .zero) (∅ :
      Set ((Fin a.arity ⊕ Fin 0) → K)) := by
    constructor
    · intro x hx
      exact (Set.notMem_empty x (ha ▸ hx)).elim
    · intro x hx
      exact (Set.notMem_empty x hx).elim
  exact FieldDefinableRing.relation_zero K (.atom a) .zero ∅ Set.definable_empty hb

theorem objectClass_unique (a : Chart K) (ha : ∃! x, x ∈ a.domain) : objectClass K a = 1 := by
  obtain ⟨x, hx, huniq⟩ := ha
  have hb : BiUnique (domain K (.atom a)) (domain K .one) (Set.univ :
      Set ((Fin a.arity ⊕ Fin 0) → K)) := by
    constructor
    · intro _ _
      exact ⟨Fin.elim0, ⟨Set.mem_univ _, Set.mem_univ _⟩,
        fun _ _ => funext (fun i : Fin 0 => i.elim0)⟩
    · intro y _
      exact ⟨x, ⟨hx, Set.mem_univ _⟩, fun z hz => huniq z hz.1⟩
  have h := FieldDefinableRing.relation_zero K (.atom a) .one Set.univ Set.definable_univ hb
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a) =
    Ideal.Quotient.mk (relationIdeal K) 1 at h
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a) = 1
  simpa only [map_one] using h

end DiamondIntegral.Section4.FieldPointCharts
