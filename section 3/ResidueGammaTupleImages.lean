import «section 3».ResidueGammaTupleColumns
import «section 3».FiniteColumnProjections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]



/-- Finite residue-valued correspondences from Gamma tuples have finite
residue image, over the original real/Gamma ground. -/
theorem residue_gamma_tuple_finite_residue_projection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n m : ℕ} (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop)
    (hR : mixedGammaTupleDefinable B R) (hsort : ∀ a γ, R a γ → ∀ i, iRV (a i))
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i)
    (hrows : ∀ γ, {a | a ∈ A ∧ R a γ}.Finite) :
    {a | a ∈ A ∧ ∃ γ, R a γ}.Finite := by
  exact finite_projection_of_finite_columns (fun γ a => R a γ) A
    (residue_gamma_tuple_finite_columns hκ hs h00 B hsmall hγsmall hΓ R hR hsort A hA D hD hvalues hsub) hrows
end DiamondIntegral.Section3
