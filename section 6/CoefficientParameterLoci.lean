import «section 6».FocusMetadataParameterLoci

/-! The nonzero coefficient and its permitted valuation range are
first-order conditions on finite focus metadata. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι : Type} [Finite ι]

def coefficientCodeCondition (ι : Type) : Set (FocusMetadataIndex ι → M) :=
  {z | z (.inl (.inr 0)) ≠ iVFZero ∧ iLe (iRv iVFOne) (iRv (z (.inl (.inr 0))))}

theorem coefficientCodeCondition_definable : S.Definable LRV (coefficientCodeCondition (M := M) ι) := by
  let Z := FocusMetadataIndex ι
  have hZero : S.Definable LRV {z : Z → M | z (.inl (.inr 0))=iVFZero} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (vfZeroCode_definable S)
  have hOne : S.DefinableFun LRV (fun _ : Z → M => iVFOne) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (show S.DefinableMap LRV (fun _ : Z → M => (Fin.elim0 : Fin 0 → M)) from fun i => i.elim0)
  exact hZero.compl.inter (rvCode_compare_definable (rv_scalarCode_definable hOne)
    (rv_scalarCode_definable (Set.DefinableFun.proj LRV)))

theorem coefficientCodeCondition_at (a : ι → M) (c : VF M) (t : RVInfinity M) :
    Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val) ∈ coefficientCodeCondition ι ↔
      c ≠ 0 ∧ (1 : GammaInfinity M) ≤ vfValue c := by
  have hNZ : c.val ≠ iVFZero ↔ c ≠ 0 := by
    change c.val ≠ (0 : VF M).val ↔ c ≠ 0
    exact not_congr Subtype.val_inj
  have hPos : iLe (rv M (1 : VF M)).val (rv M c).val ↔ (1 : GammaInfinity M) ≤ vfValue c := by
    rw [← Values.vrv_le_iff]
    change vfValue (1 : VF M) ≤ vfValue c ↔ _
    rw [show vfValue (1 : VF M)=1 from Values.vfValueHom.map_one]
  exact and_congr hNZ hPos

end DiamondIntegral.Section6
