import «section 3».IntegerCharacterFirstCoordinate
import «section 3».GammaMonomialHyperplaneImages
import «section 3».TensorFiniteFactorAbsorption
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r m : ℕ}

/-- A nonempty character-hyperplane factor loses one free Gamma coordinate
by an actual integral Gamma isomorphism and positive finite-Gamma balancing.
Its degree is transferred to RES, with no old-ground RV point assumed. -/
theorem gammaGroundUnmeasuredTensor_character_hyperplane_reduction
    (X : GammaGroundRESObject hc B r)
    (H : GammaGroundCharacterHyperplane B (1+m)) (G : GammaGroundGammaPiece hc B (1+m))
    (hG : G.carrier.Nonempty) (hsub : G.carrier ⊆ H.carrier) :
    ∃ F : GammaGroundFiniteGammaObject hc B 1, ∃ W : GammaGroundGammaPiece hc B m,
      gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        gammaGroundRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single W) := by
  obtain ⟨b,d,hd,hpow⟩ := integerCharacter_nonzero_first_basis_power H.normal H.nonzero
  obtain ⟨γ0,hγ0⟩ := hG
  change Fin (1+m) → Values.Gamma (M := M) at γ0
  let δ0 : Values.Gamma (M := M) := integerMonomialBasisEquiv b γ0 0
  have hδpow : δ0 ^ d = H.value := (hpow γ0).symm.trans (hsub hγ0)
  have hδ : GammaDefinableClosureAtBase B δ0 :=
    gammaDefinableClosure_nonzero_power_root d hd δ0 H.value H.value_definable hδpow
  let V := gammaGroundMonomialValueImage G (integerBasisMatrix b)
  have hfixed : ∀ η : Fin (1+m) → Values.Gamma (M := M), η ∈ V.carrier → η 0 = δ0 := by
    intro η hη
    obtain ⟨γ,hγ,he⟩ := (gammaGroundMonomialValueImage_mem G (integerBasisMatrix b) η).mp hη
    have hc : integerMonomialBasisEquiv b γ 0 = η 0 := congrFun he 0
    apply zpow_left_injective hd
    exact (congrArg (fun a : Values.Gamma (M := M) => a ^ d) hc).symm.trans
      ((hpow γ).symm.trans ((hsub hγ).trans hδpow.symm))
  let δ : Fin 1 → Values.Gamma (M := M) := fun _ => δ0
  have hprefix : ∀ η : Fin (1+m) → Values.Gamma (M := M),
      η ∈ V.carrier → ∀ i : Fin 1, η (Fin.castAdd m i) = δ i := by
    intro η hη i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hfixed η hη
  obtain ⟨F,W,hbalance⟩ := gammaGroundUnmeasuredTensor_fixed_prefix_absorption X V δ (fun _ => hδ) hprefix
  refine ⟨F,W,?_⟩
  rw [gammaGroundGammaSemiringClass_monomial_image G (integerBasisMatrix b) (integerBasisMatrix_det_isUnit b)]
  exact hbalance
end DiamondIntegral.Section3
