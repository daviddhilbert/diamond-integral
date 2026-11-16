import «section 6».ContinuousShears

/-! Arithmetic of definable real-code functions used to assemble the
two finite-aperture clauses and the original-base branch predicate. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {I : Type} {S : Set M}

private theorem rawNeg_definable : S.DefinableFun LRV (fun z : Fin 1 → M => iVFNeg (z 0)) := by
  have h : S.DefinableFun LRV (fun z : Fin 1 → M => Structure.funMap (L := LRV) Fn.vfNeg z) :=
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg).of_empty
  have he : (fun z : Fin 1 → M => Structure.funMap (L := LRV) Fn.vfNeg z) =
      (fun z => iVFNeg (z 0)) := by
    funext z
    apply congrArg (Structure.funMap (L := LRV) Fn.vfNeg)
    funext i
    fin_cases i
    rfl
  exact he ▸ h

private theorem rawAdd_definable : S.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd (z 0) (z 1)) := by
  have h : S.DefinableFun LRV (fun z : Fin 2 → M => Structure.funMap (L := LRV) Fn.vfAdd z) :=
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd).of_empty
  have he : (fun z : Fin 2 → M => Structure.funMap (L := LRV) Fn.vfAdd z) =
      (fun z => iVFAdd (z 0) (z 1)) := by
    funext z
    apply congrArg (Structure.funMap (L := LRV) Fn.vfAdd)
    funext i
    fin_cases i <;> rfl
  exact he ▸ h

private theorem rawMul_definable : S.DefinableFun LRV (fun z : Fin 2 → M => iVFMul (z 0) (z 1)) := by
  have h : S.DefinableFun LRV (fun z : Fin 2 → M => Structure.funMap (L := LRV) Fn.vfMul z) :=
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfMul).of_empty
  have he : (fun z : Fin 2 → M => Structure.funMap (L := LRV) Fn.vfMul z) =
      (fun z => iVFMul (z 0) (z 1)) := by
    funext z
    apply congrArg (Structure.funMap (L := LRV) Fn.vfMul)
    funext i
    fin_cases i <;> rfl
  exact he ▸ h

theorem scalarNegCode_definable {F : (I → M) → M} (hF : S.DefinableFun LRV F) :
    S.DefinableFun LRV (fun z => iVFNeg (F z)) := by
  have harg : S.DefinableMap LRV (fun z => ![F z]) := by intro i; fin_cases i; exact hF
  have h := (rawNeg_definable (M := M) (S := S)).comp harg
  exact h

theorem scalarAddCode_definable {F G : (I → M) → M}
    (hF : S.DefinableFun LRV F) (hG : S.DefinableFun LRV G) :
    S.DefinableFun LRV (fun z => iVFAdd (F z) (G z)) := by
  have harg : S.DefinableMap LRV (fun z => ![F z,G z]) := by
    intro i
    fin_cases i
    · exact hF
    · exact hG
  have h := (rawAdd_definable (M := M) (S := S)).comp harg
  exact h

theorem scalarMulCode_definable {F G : (I → M) → M}
    (hF : S.DefinableFun LRV F) (hG : S.DefinableFun LRV G) :
    S.DefinableFun LRV (fun z => iVFMul (F z) (G z)) := by
  have harg : S.DefinableMap LRV (fun z => ![F z,G z]) := by
    intro i
    fin_cases i
    · exact hF
    · exact hG
  have h := (rawMul_definable (M := M) (S := S)).comp harg
  exact h

theorem scalarSubCode_definable {F G : (I → M) → M}
    (hF : S.DefinableFun LRV F) (hG : S.DefinableFun LRV G) :
    S.DefinableFun LRV (fun z => iVFAdd (F z) (iVFNeg (G z))) :=
  scalarAddCode_definable hF (scalarNegCode_definable hG)

theorem rvCode_compare_definable {F G : (I → M) → M}
    (hF : S.DefinableFun LRV F) (hG : S.DefinableFun LRV G) :
    S.Definable LRV {z | iLe (F z) (G z)} := by
  have harg : S.DefinableMap LRV (fun z => ![F z,G z]) := by
    intro i
    fin_cases i
    · exact hF
    · exact hG
  exact (GammaParameters.raw_le_definable S).preimage_map harg

end DiamondIntegral.Section6
