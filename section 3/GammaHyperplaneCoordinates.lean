import «section 3».IntegerCharacterBasisReduction
import «section 3».GammaGenericFiniteCover
import Section3.GammaFiniteOrder
import Mathlib.Algebra.Group.Torsion
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

/-- A nonzero integral root of an old-ground definable Gamma point is
again old-ground definable. The proof uses its actual singleton root set. -/
theorem gammaDefinableClosure_nonzero_power_root
    (d : ℤ) (hd : d ≠ 0) (a δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (ha : a ^ d = δ) :
    GammaDefinableClosureAtBase B a := by
  let P : Set (Values.Gamma (M := M)) := {b | b ^ d = δ}
  have hpFull := ((FullGammaFunction.proj (integrationGammaBase B) (0 : Fin 1)).zpow d).eq
    (FullGammaFunction.constant δ (integrationGammaDefinable hδ))
  have hpScalar : FullGammaSyntax.Scalar (integrationGammaBase B) P :=
    (FullGammaSyntax.scalar_definable_iff P).mp hpFull
  have hpNative : GammaDefinableOverBase B P := (gammaScalar_definable_iff_native B P).mpr hpScalar
  have hpSub : P.Subsingleton := by
    intro b hb c hc
    exact zpow_left_injective hd (hb.trans hc.symm)
  exact (gamma_algebraic_iff_definable_base B a).mp ⟨P,hpNative,hpSub.finite,ha⟩

/-- An integral basis change turns any nonempty old-ground character
hyperplane into a set with an old-ground definable fixed coordinate.
The basis has a two-sided integral inverse, so no fractional RV map is used. -/
theorem gammaGround_character_hyperplane_fixed_coordinate
    {hc : CanonicalStructure.IsCanonical (M := M)} {n : ℕ}
    (H : GammaGroundCharacterHyperplane B n)
    (U : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (hU : U.carrier.Nonempty) (hsub : U.carrier ⊆ H.carrier) :
    ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ), ∃ j : Fin n,
      ∃ δ : Values.Gamma (M := M), GammaDefinableClosureAtBase B δ ∧
        ∀ γ : Fin n → Values.Gamma (M := M), γ ∈ U.carrier → integerMonomialBasisEquiv b γ j = δ := by
  obtain ⟨b,j,d,hd,hpow⟩ := integerCharacter_nonzero_basis_power H.normal H.nonzero
  obtain ⟨γ0,hγ0⟩ := hU
  change Fin n → Values.Gamma (M := M) at γ0
  let δ : Values.Gamma (M := M) := integerMonomialBasisEquiv b γ0 j
  have hδpow : δ ^ d = H.value := (hpow γ0).symm.trans (hsub hγ0)
  refine ⟨b,j,δ,gammaDefinableClosure_nonzero_power_root d hd δ H.value H.value_definable hδpow,?_⟩
  intro γ hγ
  apply zpow_left_injective hd
  exact (hpow γ).symm.trans ((hsub hγ).trans hδpow.symm)
end DiamondIntegral.Section3
