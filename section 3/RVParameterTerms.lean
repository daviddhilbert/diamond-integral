import «section 3».RVDefinableDNF
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def parameterTermFunction (p : Parameters S) (t : LRV.Term (Fin p.length ⊕ Fin n)) (z : Fin n → M) : M :=
  t.realize (Sum.elim p.values z)

theorem parameterTermFunction_definable (p : Parameters S) (t : LRV.Term (Fin p.length ⊕ Fin n)) :
    S.DefinableFun LRV (parameterTermFunction p t) := by
  apply (Set.DefinableFun.of_empty t.definableFun_realize).comp
  intro i
  cases i with
  | inl i => exact LRV.definableFun_const (Fin n) (p.mem_base i)
  | inr i => exact Set.DefinableFun.proj LRV

def rvMonomialParameterTerm (p : Parameters S)
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    LRV.Term (Fin p.length ⊕ Fin n) :=
  T.expression.toTerm (vfSlotMap p.sorts (fun _ : Fin n => .rv)) (rvParameterMap p.sorts) Sum.inr

theorem rvMonomialParameterTerm_realize (p : Parameters S)
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (y : Fin n → CanonicalRV.RVSort M) :
    parameterTermFunction p (rvMonomialParameterTerm p T) (rvValues y) =
      (T.rawEval (sourceVFFixedValues p n) (sourceRVFixedParameters p) y).val := by
  let z := rvValues y
  have hz : ∀ i, sortEval SortTag.rv (z i) := fun i => (y i).property
  have hf := sourceVF_allRV_independent p z hz
  have hv (i : VFSlot p.sorts (fun _ : Fin n => .rv)) :
      Sum.elim p.values z (vfSlotMap p.sorts (fun _ : Fin n => .rv) i) = (sourceVFFixedValues p n i).val :=
    congrArg Subtype.val (congrFun hf i)
  have hh := RVExpr.toTerm_realize (vfSlotMap p.sorts (fun _ : Fin n => .rv)) (rvParameterMap p.sorts)
    (Sum.inr : Fin n → Fin p.length ⊕ Fin n) (Sum.elim p.values z)
    (sourceVFFixedValues p n) (sourceRVFixedParameters p) y hv (fun _ => rfl) (fun _ => rfl) T.expression
  rw [Monomial.expression_eval] at hh
  exact hh
end DiamondIntegral.Section3
