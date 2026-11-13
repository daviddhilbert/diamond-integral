import «section 3».MeasuredGammaFibreDescent
import «section 3».GammaGroundIntegralMonomialImages
import «section 3».GammaGroundMeasuredGammaSemiring
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Pure unimodular monomials carry any compatible prescribed full
combined weights by a genuine measured Gamma morphism. -/
def gammaGroundMeasuredGammaSingleMonomialHom (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (hh : FullGammaFunction (integrationGammaBase B) h)
    (hw : ∀ γ ∈ G.carrier, f γ = h (integerMonomialMap A γ)) :
    GammaGroundMeasuredGammaHom (gammaGroundMeasuredGammaSingleWeight G f hf)
      (gammaGroundMeasuredGammaSingleWeight (gammaGroundMonomialValueImage G A) h hh) := by
  let F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G)
      (gammaGroundRVUnitGammaPreimage (gammaGroundMonomialValueImage G A)) :=
    ⟨gammaGroundIntegralMonomialMap G A,gammaGroundIntegralMonomialMap_bijective G A hA⟩
  refine gammaGroundMeasuredGammaSingleHomOfWeightUnitBijection G (gammaGroundMonomialValueImage G A) F ?_ f h hf hh ?_
  · intro u v
    change rvUnitTupleValues u.val = rvUnitTupleValues v.val ↔
      rvUnitTupleValues (integerMonomialMap A u.val) = rvUnitTupleValues (integerMonomialMap A v.val)
    have he := (affineMonomial_value_kernel_iff (rvUnitValueHom (M := M)) A hA 1 u.val v.val).symm
    simp only [one_mul] at he
    exact he
  · intro u
    change f (rvUnitTupleValues u.val) = h (rvUnitTupleValues (integerMonomialMap A u.val))
    have hv : rvUnitTupleValues (integerMonomialMap A u.val) = integerMonomialMap A (rvUnitTupleValues u.val) :=
      monomial_map_value (rvUnitValueHom (M := M)) A u.val
    exact (hw _ u.property).trans (congrArg h hv).symm

theorem gammaGroundMeasuredGammaSemiringClass_monomial_weight (G : GammaGroundGammaPiece hc B n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (hh : FullGammaFunction (integrationGammaBase B) h)
    (hw : ∀ γ ∈ G.carrier, f γ = h (integerMonomialMap A γ)) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (gammaGroundMonomialValueImage G A) h hh) :=
  gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from
    gammaGroundMeasuredGammaSingleMonomialHom G A hA f h hf hh hw))
end DiamondIntegral.Section3
