import «section 3».RVCoefficientNames
import «section 3».RVMonomialValueDependence
import «section 3».FullGammaFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def monomialGammaExpression (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hT : rvMonomialCoefficient T a r ≠ 0) (γ : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  rvUnitValueHom (Units.mk0 (rvMonomialCoefficient T a r) hT) * integerCharacter (fun i => T.powers i) γ

theorem monomialGammaExpression_semantics (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hT : rvMonomialCoefficient T a r ≠ 0) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    monomialGammaExpression T a r hT (fun i => rvUnitValueHom (x i)) =
      rvUnitValueHom (Units.mk0 (rvMonomialCoefficient T a r) hT * integerCharacter (fun i => T.powers i) x) := by
  simp only [monomialGammaExpression,map_mul,integerCharacter,map_prod,map_zpow]

theorem monomialGammaExpression_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (hT : rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p) ≠ 0) :
    FullGammaFunction (integrationGammaBase B)
      (monomialGammaExpression T (sourceVFFixedValues p n) (sourceRVFixedParameters p) hT) := by
  have hδ := rvMonomialCoefficient_value_original_ground hκ hs h00 hc B hsmall p T hT
  have hcst := FullGammaFunction.constant (α := Fin n) _ (integrationGammaDefinable hδ)
  have hchar := FullGammaFunction.prod (B := integrationGammaBase B) Finset.univ
    (fun i γ => γ i ^ T.powers i) (fun i _ => (FullGammaFunction.proj _ i).zpow (T.powers i))
  exact hcst.mul hchar

def monomialGammaResidue (T : Monomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (γ : Fin n → Values.Gamma (M := M)) : Prop :=
  if hT : rvMonomialCoefficient T a r = 0 then True else monomialGammaExpression T a r hT γ = 1

theorem monomialGammaResidue_semantics (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    monomialGammaResidue T a r (fun i => rvUnitValueHom (x i)) ↔
      ValuedModelMap.inK (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) := by
  by_cases hT : rvMonomialCoefficient T a r = 0
  · simp only [monomialGammaResidue,dite_eq_left hT,rvMonomial_zero_coefficient T a r hT]
    exact ⟨fun _ => Or.inr (Subtype.ext RVOperations.zero_val),fun _ => trivial⟩
  · rw [monomialGammaResidue,dite_eq_right hT,monomialGammaExpression_semantics,rvUnitValue_eq_one_iff_inK]
    have he : ((Units.mk0 (rvMonomialCoefficient T a r) hT * integerCharacter (fun i => T.powers i) x : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M) =
        T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) := (rvMonomial_rawEval_units T a r x).symm
    rw [he]

theorem monomialGammaResidue_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    FullGammaSyntax.Definable (integrationGammaBase B)
      (monomialGammaResidue T (sourceVFFixedValues p n) (sourceRVFixedParameters p)) := by
  by_cases hT : rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p) = 0
  · apply (FullGammaSyntax.Definable.true_ (ι := Fin n) (integrationGammaBase B)).congr
    intro γ
    simp only [monomialGammaResidue,dite_eq_left hT]
  · apply ((monomialGammaExpression_definable hκ hs h00 hc B hsmall p T hT).eq (FullGammaFunction.one _)).congr
    intro γ
    simp only [monomialGammaResidue,dite_eq_right hT]

def monomialGammaEqualValue (T U : Monomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (γ : Fin n → Values.Gamma (M := M)) : Prop :=
  if hT : rvMonomialCoefficient T a r = 0 then rvMonomialCoefficient U a r = 0
  else if hU : rvMonomialCoefficient U a r = 0 then False
  else monomialGammaExpression T a r hT γ = monomialGammaExpression U a r hU γ

theorem monomialGammaEqualValue_semantics (T U : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    monomialGammaEqualValue T U a r (fun i => rvUnitValueHom (x i)) ↔
      RVOperations.absoluteHom (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
      RVOperations.absoluteHom (U.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) := by
  by_cases hT : rvMonomialCoefficient T a r = 0
  · rw [monomialGammaEqualValue,dite_eq_left hT,rvMonomial_zero_coefficient T a r hT,map_zero]
    conv_rhs => rw [eq_comm,RVOperations.absolute_eq_zero,rvMonomial_rawEval_units]
    exact (mul_eq_zero.trans (or_iff_left (Units.ne_zero _))).symm
  · by_cases hU : rvMonomialCoefficient U a r = 0
    · rw [monomialGammaEqualValue,dite_eq_right hT,dite_eq_left hU,rvMonomial_zero_coefficient U a r hU,map_zero,RVOperations.absolute_eq_zero]
      exact iff_of_false False.elim (rvMonomial_rawEval_ne_zero T a r hT x)
    · rw [monomialGammaEqualValue,dite_eq_right hT,dite_eq_right hU,monomialGammaExpression_semantics,monomialGammaExpression_semantics,rvUnitValue_eq_iff_absolute_eq]
      rw [rvMonomial_rawEval_units,rvMonomial_rawEval_units]
      rfl

theorem monomialGammaEqualValue_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (T U : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    FullGammaSyntax.Definable (integrationGammaBase B)
      (monomialGammaEqualValue T U (sourceVFFixedValues p n) (sourceRVFixedParameters p)) := by
  have htrue := FullGammaSyntax.Definable.true_ (ι := Fin n) (integrationGammaBase B)
  have hfalse : FullGammaSyntax.Definable (integrationGammaBase B) (fun _ : Fin n → Values.Gamma (M := M) => False) :=
    htrue.not.congr (fun _ => by simp)
  by_cases hT : rvMonomialCoefficient T (sourceVFFixedValues p n) (sourceRVFixedParameters p) = 0
  · by_cases hU : rvMonomialCoefficient U (sourceVFFixedValues p n) (sourceRVFixedParameters p) = 0
    · apply htrue.congr
      intro γ
      simp only [monomialGammaEqualValue,dite_eq_left hT,hU]
    · apply hfalse.congr
      intro γ
      simp only [monomialGammaEqualValue,dite_eq_left hT,hU]
  · by_cases hU : rvMonomialCoefficient U (sourceVFFixedValues p n) (sourceRVFixedParameters p) = 0
    · apply hfalse.congr
      intro γ
      simp only [monomialGammaEqualValue,dite_eq_right hT,dite_eq_left hU]
    · apply ((monomialGammaExpression_definable hκ hs h00 hc B hsmall p T hT).eq
          (monomialGammaExpression_definable hκ hs h00 hc B hsmall p U hU)).congr
      intro γ
      simp only [monomialGammaEqualValue,dite_eq_right hT,dite_eq_right hU]
end DiamondIntegral.Section3
