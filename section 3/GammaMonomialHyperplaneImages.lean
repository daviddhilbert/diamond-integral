import «section 3».GammaHyperplaneCoordinates
import «section 3».GammaGroundIntegralMonomialImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- The integral basis matrix has an actual two-sided integral inverse. -/
theorem integerBasisMatrix_det_isUnit (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    IsUnit (integerBasisMatrix b).det := by
  apply (Matrix.isUnit_iff_isUnit_det (integerBasisMatrix b)).mp
  exact ⟨⟨integerBasisMatrix b,integerBasisInverseMatrix b,
    integerBasis_mul_inverse b,integerBasisInverse_mul b⟩,rfl⟩

/-- A nonempty character-hyperplane piece is positively Gamma-isomorphic
to an actual integral monomial image with an old-ground fixed coordinate. -/
theorem gammaGroundGamma_character_hyperplane_image
    (H : GammaGroundCharacterHyperplane B n) (G : GammaGroundGammaPiece hc B n)
    (hG : G.carrier.Nonempty) (hsub : G.carrier ⊆ H.carrier) :
    ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ), ∃ j : Fin n,
      ∃ δ : Values.Gamma (M := M), GammaDefinableClosureAtBase B δ ∧
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        gammaGroundGammaSemiringClass
          (GammaGroundGammaObject.single (gammaGroundMonomialValueImage G (integerBasisMatrix b))) ∧
      ∀ η : Fin n → Values.Gamma (M := M),
        η ∈ (gammaGroundMonomialValueImage G (integerBasisMatrix b)).carrier → η j = δ := by
  obtain ⟨b,j,δ,hδ,hfixed⟩ := gammaGround_character_hyperplane_fixed_coordinate H G hG hsub
  refine ⟨b,j,δ,hδ,gammaGroundGammaSemiringClass_monomial_image G
    (integerBasisMatrix b) (integerBasisMatrix_det_isUnit b),?_⟩
  intro η hη
  obtain ⟨γ,hγ,hγη⟩ := (gammaGroundMonomialValueImage_mem G (integerBasisMatrix b) η).mp hη
  have hcoord : integerMonomialMap (integerBasisMatrix b) γ j = δ := hfixed γ hγ
  exact (congrFun hγη j).symm.trans hcoord
end DiamondIntegral.Section3
