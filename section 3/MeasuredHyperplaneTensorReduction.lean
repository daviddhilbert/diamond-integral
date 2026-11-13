import «section 3».IntegerCharacterFirstCoordinate
import «section 3».GammaMonomialHyperplaneImages
import «section 3».MeasuredGammaFixedPrefixProducts
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

/-- Pullback by an integral monomial matrix retains full Gamma
definability over the original ground. -/
theorem fullGammaFunction_monomial_pullback {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    FullGammaFunction (integrationGammaBase B) (fun γ => f (integerMonomialMap A γ)) :=
  hf.comp (fun i γ => integerMonomialMap A γ i) (fun i =>
    FullGammaFunction.prod Finset.univ (fun j γ => γ j ^ A i j)
      (fun j _ => (FullGammaFunction.proj _ j).zpow (A i j)))

/-- A nonempty character-hyperplane factor loses one free Gamma coordinate
by an actual integral Gamma isomorphism and positive finite-Gamma balancing.
Its degree is transferred to RES, with no old-ground RV point assumed. -/
theorem gammaGroundMeasuredTensor_character_hyperplane_reduction
    (X : GammaGroundMeasuredRESObject hc B r)
    (H : GammaGroundCharacterHyperplane B (1+m)) (G : GammaGroundGammaPiece hc B (1+m))
    (hG : G.carrier.Nonempty) (hsub : G.carrier ⊆ H.carrier)
    (f : (Fin (1+m) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    ∃ F : GammaGroundMeasuredFiniteGammaObject hc B 1, ∃ W : GammaGroundGammaPiece hc B m,
      ∃ w : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M),
      ∃ hw : FullGammaFunction (integrationGammaBase B) w,
      gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
        gammaGroundMeasuredRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight W w hw) := by
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
  let w : (Fin (1+m) → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
    fun η => f (integerMonomialMap (integerBasisInverseMatrix b) η)
  have hw : FullGammaFunction (integrationGammaBase B) w :=
    fullGammaFunction_monomial_pullback f hf (integerBasisInverseMatrix b)
  obtain ⟨F,W,hbalance⟩ := gammaGroundMeasuredTensor_fixed_prefix_absorption X V δ (fun _ => hδ) hprefix w hw
  refine ⟨F,W,gammaGroundPrefixRestrictedWeight w δ,gammaGroundPrefixRestrictedWeight_definable w hw δ (fun _ => hδ),?_⟩
  have hmono := gammaGroundMeasuredGammaSemiringClass_monomial_weight G (integerBasisMatrix b)
    (integerBasisMatrix_det_isUnit b) f w hf hw (by
      intro γ _
      change f γ = f (integerMonomialMap (integerBasisInverseMatrix b) (integerMonomialMap (integerBasisMatrix b) γ))
      rw [integerMonomialMap_comp,integerBasisInverse_mul,integerMonomialMap_one])
  exact (congrArg (fun a => gammaGroundMeasuredRESDirectSumClass X
    ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B] a) hmono).trans hbalance
end DiamondIntegral.Section3
