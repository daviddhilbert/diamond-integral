import «section 3».RVParameterTerms
import «section 3».RVMonomialCharacters
import «section 3».TermGammaValue
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvMonomialCoefficient_raw_definable (p : Parameters S)
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    S.Definable₁ LRV {(rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p)).val} := by
  let T0 : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n) := {T with powers := 0}
  let y : Fin n → CanonicalRV.RVSort M := fun _ => 1
  have hy : rvValues y = fun _ : Fin n => iRVOne := by
    funext i
    exact RVOperations.one_val
  have he : T0.rawEval (sourceVFFixedValues p n) (sourceRVFixedParameters p) y =
      rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p) := by
    simp only [T0,Monomial.rawEval,rvMonomialCoefficient,Finsupp.prod_zero_index,mul_one]
  have ht := rvMonomialParameterTerm_realize p T0 y
  rw [hy,he] at ht
  have hone : S.Definable₁ LRV {iRVOne (M := M)} :=
    SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.rvOne Fin.elim0 (fun i => i.elim0)
  have hmap : S.DefinableMap LRV (fun _ : Fin 0 → M => fun _ : Fin n => iRVOne) :=
    fun _ => SpecialTransformations.DefinableConstants.constant hone
  have hd := (parameterTermFunction_definable p (rvMonomialParameterTerm p T0)).comp hmap
  have hs := SpecialTransformations.DefinableConstants.singleton_of_constant hd
  rw [ht] at hs
  exact hs

theorem rvMonomialCoefficient_definable (hc : CanonicalStructure.IsCanonical (M := M)) (p : Parameters S)
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    DefinableClosureAt S .rv (rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p)).val := by
  apply (definableAt_iff_normalized_raw S .rv _).mpr
  constructor
  · rw [canonical_normalize_eq hc]
    exact rvMonomialCoefficient_raw_definable p T
  · rintro t ht
    have he := Set.mem_singleton_iff.mp ht
    subst t
    exact (rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p)).property

/-- Every nonzero coefficient value in a common-name normal form is
Gamma-definable over the original real/Gamma ground. -/
theorem rvMonomialCoefficient_value_original_ground {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (hT : rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p) ≠ 0) :
    GammaDefinableClosureAtBase B (Values.gammaOf
      (rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p))
      (fun h => hT (Subtype.ext (h.trans RVOperations.zero_val.symm)))) :=
  common_names_gamma_definable_elimination hκ hs h00 B hsmall _
    (gamma_value_definable_of_rv_definable _ _ hT (rvMonomialCoefficient_definable hc p T))
end DiamondIntegral.Section3
