import «section 3».TorusWeightQuotientLifts
import «section 3».GammaGroundPointTranslations
import «section 3».GammaGroundIntegralMonomialImages
import «section 3».RESCoefficientNeighborhoods
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- The quotient by actual definable RV values produces actual
original-ground coefficients and a definable singleton tuple of them. -/
theorem gammaGroundTorusWeight_coefficients
    (a b : Fin n → Values.Gamma (M := M)) (C : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, QuotientGroup.mk' (gammaGroundDefinableRVValues B) (b i) =
      integerMonomialMap C
        (fun j => QuotientGroup.mk' (gammaGroundDefinableRVValues B) (a j)) i) :
    ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ i, DefinableClosureAtBase B .rv (rvUnitValues c i)) ∧
      b = rvUnitTupleValues c * integerMonomialMap C a ∧
      GammaGroundDefinable hc B (rawRVUnitSpace n) {c} := by
  obtain ⟨c,hcdef,hcval⟩ := monomial_coefficients_of_quotient_weights
    (rvUnitValueHom (M := M)) (gammaGroundRVDefinableUnits B) a b C h
  exact ⟨c,hcdef,hcval,gammaGroundRVUnitTuple_point_definable c hcdef⟩

/-- A unimodular monomial followed by an actual old-ground multiplier
is a full-preimage bijection, on its entire prescribed Gamma image. -/
def gammaGroundRVUnitAffinePointBijection (G H : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsUnit C.det)
    (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c})
    (hshift : ∀ γ : Fin n → Values.Gamma (M := M),
      γ ∈ (gammaGroundMonomialValueImage G C).carrier ↔
        (fun i => rvUnitValueHom (c i) * γ i) ∈ H.carrier) :
    GammaGroundBijection (gammaGroundRVUnitGammaPreimage G)
      (gammaGroundRVUnitGammaPreimage H) :=
  (gammaGroundRVUnitPointTranslation (gammaGroundMonomialValueImage G C) H c hcdef hshift).comp
    ⟨gammaGroundIntegralMonomialMap G C,gammaGroundIntegralMonomialMap_bijective G C hC⟩

@[simp] theorem gammaGroundRVUnitAffinePointBijection_formula
    (G H : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsUnit C.det)
    (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c})
    (hshift : ∀ γ : Fin n → Values.Gamma (M := M),
      γ ∈ (gammaGroundMonomialValueImage G C).carrier ↔
        (fun i => rvUnitValueHom (c i) * γ i) ∈ H.carrier)
    (u : gammaGroundRVUnitGammaPreimage G) :
    ((gammaGroundRVUnitAffinePointBijection G H C hC c hcdef hshift).map u).val =
      c * integerMonomialMap C u.val := rfl

def gammaGroundGammaSingleAffinePointHom (G H : GammaGroundGammaPiece hc B n)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsUnit C.det)
    (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c})
    (hshift : ∀ γ : Fin n → Values.Gamma (M := M),
      γ ∈ (gammaGroundMonomialValueImage G C).carrier ↔
        (fun i => rvUnitValueHom (c i) * γ i) ∈ H.carrier) :
    GammaGroundGammaObject.single G ⟶ GammaGroundGammaObject.single H :=
  gammaGroundGammaSingleHomOfAffineMonomial G H
    (gammaGroundRVUnitAffinePointBijection G H C hC c hcdef hshift) C hC c
    (fun _ => rfl)

end DiamondIntegral.Section3
