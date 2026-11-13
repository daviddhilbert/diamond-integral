import «section 4».RVMeasuredCharts

/-! The RV point choice in Notation 4.13. Two original-base definable
proper RV points of the same value are isomorphic with constant zero
volume form. The graph and volume equation are checked on actual points;
no representative is added to the original parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVPointChoices
open RVMeasuredCharts FiniteTupleBlocks GammaGroupNames

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem point_tuple_definable (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) :
    DefinableOverBase B (fun _ : Fin 1 => .rv) ({![raw t]} : Set (Fin 1 → M)) :=
  tuple_singleton_definable_base B (fun _ => .rv) ![raw t] (by intro i; fin_cases i; exact ht)

theorem pair_tuple_definable (B : Base (M := M)) (t u : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (hu : DefinableClosureAtBase B .rv (raw u)) :
    DefinableOverBase B (fun _ : Fin 2 => .rv) ({![raw t, raw u]} : Set (Fin 2 → M)) :=
  tuple_singleton_definable_base B (fun _ => .rv) ![raw t, raw u]
    (by intro i; fin_cases i; exact ht; exact hu)

def pointChart (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) : Chart B 1 where
  arity := 1
  domain := {![raw t]}
  domain_definable := point_tuple_definable B t ht
  coordinate := id
  coordinate_definable := by
    have h := pair_tuple_definable B t t ht ht
    convert h using 1
    ext w
    simp only [graphOn, Set.mem_ofPred_eq, Set.mem_singleton_iff, id_eq, funext_iff,
      Fin.forall_fin_succ, headIndex, tailIndex]
    simp
    intro hw
    rw [hw]
    exact eq_comm
  coordinate_proper := by
    intro z hz i
    have hz' : z = ![raw t] := hz
    subst z
    fin_cases i
    exact ⟨raw_rv t, raw_ne_zero t⟩
  finite_fibres := by
    intro c
    exact (Set.finite_singleton ![raw t]).subset (fun _ h => h.1)
  volume := fun _ => 1
  volume_definable := constant_volume_definable B _ (point_tuple_definable B t ht) 1 (one_definable_base B)

theorem pointChart_weight (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (z : (pointChart B t ht).domain) :
    (pointChart B t ht).correctedWeight z.val = value t := by
  have hz : z.val = ![raw t] := z.property
  change 1 * (∏ i : Fin 1, codeValue (z.val i)) = value t
  rw [hz, Fin.prod_univ_one, one_mul]
  exact codeValue_raw t

def same_value_iso (B : Base (M := M)) (t u : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) (hu : DefinableClosureAtBase B .rv (raw u))
    (hval : value t = value u) : Iso (pointChart B t ht) (pointChart B u hu) where
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
  weight_eq := by
    intro z
    exact (pointChart_weight B t ht z).trans (hval.trans (pointChart_weight B u hu _).symm)

theorem pointChart_finite_values (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) :
    (Set.range (pointChart B t ht).valuePattern).Finite := by
  have hf : (pointChart B t ht).domain.Finite := Set.finite_singleton _
  let : Finite (pointChart B t ht).domain := hf
  exact Set.finite_range _

def pointRESChart (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) : RESChart B 1 :=
  ⟨pointChart B t ht, pointChart_finite_values B t ht⟩

end DiamondIntegral.Section4.RVPointChoices
