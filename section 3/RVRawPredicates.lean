import Section3.GammaCodeDefinability
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M α : Type} [LRV.Structure M] [Finite α] {S : Set M}

theorem rvRaw_le_definable (f g : (α → M) → M) (hf : S.DefinableFun LRV f) (hg : S.DefinableFun LRV g) :
    S.Definable LRV {z | iLe (f z) (g z)} := by
  have hm : S.DefinableMap LRV (fun z : α → M => ![f z,g z]) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  exact (raw_le_definable S).preimage_map hm

theorem rvRaw_same_value_definable (f g : (α → M) → M) (hf : S.DefinableFun LRV f) (hg : S.DefinableFun LRV g) :
    S.Definable LRV {z | iLe (f z) (g z) ∧ iLe (g z) (f z)} :=
  (rvRaw_le_definable f g hf hg).inter (rvRaw_le_definable g f hg hf)

theorem rvRaw_units_definable (f : (α → M) → M) (hf : S.DefinableFun LRV f) :
    S.Definable LRV {z | iUnits (f z)} := by
  have h : (∅ : Set M).Definable LRV {z : Fin 1 → M | Structure.RelMap (L := LRV) Rel.memUnits z} :=
    Set.empty_definable_iff.mpr ⟨.rel Rel.memUnits (fun i => .var (.inl i)),rfl⟩
  have hh := (h.mono (Set.empty_subset S)).preimage_map (show S.DefinableMap LRV (fun z : α → M => ![f z]) from
    fun i => by have hi : i = (0 : Fin 1) := Subsingleton.elim _ _; subst i; exact hf)
  exact hh

theorem rvRaw_inK_definable (f : (α → M) → M) (hf : S.DefinableFun LRV f) :
    S.Definable LRV {z | iUnits (f z) ∨ f z = iRVZero} := by
  have hz : S.DefinableFun LRV (fun _ : α → M => iRVZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.rvZero Fin.elim0 (fun i => i.elim0))
  exact (rvRaw_units_definable f hf).union (hf.ofPred_eq hz)

theorem rawPredicate_bool_pattern {P : (α → M) → Prop} (hP : S.Definable LRV {z | P z}) (b : Bool) :
    S.Definable LRV {z | P z ↔ b = true} := by
  cases b
  · simpa only [Bool.false_eq_true,iff_false,Set.compl_setOf] using hP.compl
  · simpa only [iff_true] using hP
end DiamondIntegral.Section3
