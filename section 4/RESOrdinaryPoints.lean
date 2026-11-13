import «section 4».RESOrdinaryReduction
import «section 4».RVPointChoices

/-! Any two original-base definable proper RV points have equal ordinary
RES classes. Their values may differ; only the volume-free isomorphism is
used. This is the actual singleton cancellation in the radius calculation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESOrdinaryPoints
open RVPointChoices RVForgetScissors FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pointIso (B : Base (M := M)) (t u : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (hu : DefinableClosureAtBase B .rv (raw u)) :
    UnderlyingIso (pointChart B t ht) (pointChart B u hu) where
  equiv :=
    { toFun := fun _ => ⟨![raw u], Set.mem_singleton _⟩
      invFun := fun _ => ⟨![raw t], Set.mem_singleton _⟩
      left_inv := fun z => Subtype.ext z.property.symm
      right_inv := fun z => Subtype.ext z.property.symm }
  graph_definable := by
    have h := pair_tuple_definable B t u ht hu
    change DefinableOverBase B (fun _ : Fin 2 => .rv)
      {w | ∃ z : ({![raw t]} : Set (Fin 1 → M)), w = join 1 1 z.val ![raw u]}
    convert h using 1
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      have hz : z.val = ![raw t] := z.property
      rw [hz]
      rfl
    · intro hw
      have hw' : w = ![raw t, raw u] := hw
      exact ⟨⟨![raw t], Set.mem_singleton _⟩, hw'⟩

theorem point_classes (B : Base (M := M)) (t u : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (hu : DefinableClosureAtBase B .rv (raw u)) :
    RESOrdinaryRing.objectClass (pointRESChart B t ht) = RESOrdinaryRing.objectClass (pointRESChart B u hu) :=
  RESOrdinaryRing.objectClass_iso (pointIso B t u ht hu)

theorem forget_point_classes (B : Base (M := M)) (t u : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (hu : DefinableClosureAtBase B .rv (raw u)) :
    RESOrdinaryReduction.forget B (RESChartRing.objectClass (pointRESChart B t ht)) =
      RESOrdinaryReduction.forget B (RESChartRing.objectClass (pointRESChart B u hu)) := by
  rw [RESOrdinaryReduction.forget_objectClass, RESOrdinaryReduction.forget_objectClass]
  exact congrArg (RESOrdinaryReduction.quotient B) (point_classes B t u ht hu)

end DiamondIntegral.Section4.RESOrdinaryPoints
