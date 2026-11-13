import «section 4».GammaSingletonProfiles
import «section 4».GammaBoundedSpecialization
import «section 4».GammaBoundedProducts

/-! The actual bounded homogeneous polynomial of a weighted Gamma
singleton. The proof uses the injective bounded-source inclusion and the
already computed actual singleton profile; no RV lift is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedSingletonProfiles
open GammaDefinableEuler GammaBoundedFunctions GammaBoundedPolynomial GammaSingletonProfiles

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem singleton_bounded (α : Values.Gamma (M := M)) :
    GammaBoundedProducts.DomainBounded {z : Fin 1 → Values.Gamma (M := M) | z 0 = α} := by
  refine ⟨max α α⁻¹, ?_⟩
  intro z hz i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (max α α⁻¹)⁻¹ ≤ z 0 ∧ z 0 ≤ max α α⁻¹
  rw [hz]
  have hl : (max α α⁻¹)⁻¹ ≤ α := by
    simpa only [inv_inv] using inv_le_inv_iff.mpr (le_max_right α α⁻¹)
  exact ⟨hl, le_max_left α α⁻¹⟩

theorem toUnbounded_pointMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (a : Name B) :
    toUnbounded B k (GammaBoundedSpecialization.pointMonomial B k n a) =
      GammaUnboundedSpecialization.pointMonomial B k n (⟨a.val, a.property⟩ : GammaNamesSubgroup.additiveNames B) := by
  apply Subtype.ext
  change Polynomial.map (forgetBounded B k) (Polynomial.monomial n (basePoint B k a)) = Polynomial.monomial n _
  rw [Polynomial.map_monomial]
  rfl

theorem objectPolynomial_singleton (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    GammaBoundedObjectPolynomial.objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k 1
      {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (GammaDefinableMaps.constant_definable (n := 0) B α hα) (fun _ => β) (GammaDefinableMaps.constant_definable B β hβ)
      (singleton_bounded α) =
      GammaBoundedSpecialization.pointMonomial B k 1
        ⟨toPaperGamma (α * β), GammaGroupNames.mul_definable_base B α β hα hβ⟩ := by
  apply toUnbounded_injective B k
  have hp := GammaBoundedObjectPolynomial.toUnbounded_objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k 1
    {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
    (GammaDefinableMaps.constant_definable (n := 0) B α hα) (fun _ => β) (GammaDefinableMaps.constant_definable B β hβ)
    (singleton_bounded α)
  exact hp.trans ((GammaSingletonProfiles.objectPolynomial_singleton h00 hκ hs B hr hγ k α β hα hβ).trans
    (toUnbounded_pointMonomial B k 1 ⟨toPaperGamma (α * β), GammaGroupNames.mul_definable_base B α β hα hβ⟩).symm)

end DiamondIntegral.Section4.GammaBoundedSingletonProfiles
