import «section 2».Conventions
import Section3.DefinableConstants
import Section3.SortedInverseClosure

/-! The reciprocal chart uses a definable VF inverse, although inverse
is not a function symbol of LRV. Its total raw extension is zero off VF. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def rawVFInverse (x : M) : M := by
  classical
  exact if h : iVF x then (vfInvFun (M := M) ⟨x,h⟩).val else iVFZero

theorem rawVFInverse_vf (x : VF M) : rawVFInverse x.val = (x⁻¹).val := by
  simp only [rawVFInverse,dite_eq_left x.property]
  rfl

theorem rawVFInverse_graph_iff (x y : M) :
    y = rawVFInverse x ↔
      (iVF x ∧ iVF y ∧ ((x = iVFZero ∧ y = iVFZero) ∨ iVFMul x y = iVFOne)) ∨
        (¬ iVF x ∧ y = iVFZero) := by
  classical
  constructor
  · rintro rfl
    by_cases hx : iVF x
    · let a : VF M := ⟨x,hx⟩
      have hi : rawVFInverse x = (a⁻¹).val := rawVFInverse_vf a
      refine Or.inl ⟨hx,hi.symm ▸ (a⁻¹).property,?_⟩
      by_cases ha0 : a = 0
      · left
        exact ⟨congrArg Subtype.val ha0,by rw [hi,ha0,inv_zero]; rfl⟩
      · right
        rw [hi]
        have hm : a*a⁻¹ = (1 : VF M) := mul_inv_cancel₀ ha0
        exact congrArg (fun z : VF M => z.val) hm
    · exact Or.inr ⟨hx,by simp only [rawVFInverse,dif_neg hx]⟩
  · rintro (⟨hx,hy,hzero | hprod⟩ | ⟨hx,rfl⟩)
    · obtain ⟨rfl,rfl⟩ := hzero
      change (0 : VF M).val = rawVFInverse (0 : VF M).val
      rw [rawVFInverse_vf,inv_zero]
    · let a : VF M := ⟨x,hx⟩
      let b : VF M := ⟨y,hy⟩
      have hab : a*b = 1 := Subtype.ext hprod
      have ha0 : a ≠ 0 := by
        intro he
        rw [he,zero_mul] at hab
        exact zero_ne_one hab
      have hb : b = a⁻¹ := by
        calc
          b = a⁻¹*(a*b) := by rw [← mul_assoc,inv_mul_cancel₀ ha0,one_mul]
          _ = a⁻¹ := by rw [hab,mul_one]
      exact (congrArg Subtype.val hb).trans (rawVFInverse_vf a).symm
    · simp only [rawVFInverse,dif_neg hx]

theorem rawVFInverse_definable (S : Set M) {ι : Type} (j : ι) :
    S.DefinableFun LRV (fun z : ι → M => rawVFInverse (z j)) := by
  have hz : S.DefinableFun LRV (fun _ : Option ι → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have ho : S.DefinableFun LRV (fun _ : Option ι → M => iVFOne) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  have hx := ((definableAt_sort S .vf).raw_definable).preimage_comp
    (fun _ : Fin 1 => (some j : Option ι))
  have hy := ((definableAt_sort S .vf).raw_definable).preimage_comp
    (fun _ : Fin 1 => (none : Option ι))
  have hx0 := (Set.DefinableFun.proj LRV (i := some j)).ofPred_eq hz
  have hy0 := (Set.DefinableFun.proj LRV (i := (none : Option ι))).ofPred_eq hz
  have hmul : S.DefinableFun LRV
      (fun z : Option ι → M => iVFMul (z (some j)) (z none)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfMul)).comp
      (show S.DefinableMap LRV (fun z : Option ι → M => ![z (some j),z none]) from by
        intro i
        fin_cases i <;> exact Set.DefinableFun.proj LRV)
  have hprod := hmul.ofPred_eq ho
  change S.Definable LRV (Function.tupleGraph (fun z : ι → M => rawVFInverse (z j)))
  convert ((hx.inter hy).inter ((hx0.inter hy0).union hprod)).union (hx.compl.inter hy0) using 1
  ext z
  change rawVFInverse (z (some j)) = z none ↔
    ((iVF (z (some j)) ∧ iVF (z none)) ∧
      ((z (some j) = iVFZero ∧ z none = iVFZero) ∨ iVFMul (z (some j)) (z none) = iVFOne)) ∨
      (¬ iVF (z (some j)) ∧ z none = iVFZero)
  simpa only [and_assoc] using
    ((eq_comm : rawVFInverse (z (some j)) = z none ↔ z none = rawVFInverse (z (some j))).trans
      (rawVFInverse_graph_iff (z (some j)) (z none)))

end DiamondIntegral.Section2
