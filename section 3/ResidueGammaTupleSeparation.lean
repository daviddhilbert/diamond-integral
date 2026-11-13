import «section 3».MixedGammaTupleLogic
import «section 3».ResiduePairGammaClosure
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



/-- Differing Gamma-tuple columns of residue tuples are separated by a
Gamma tuple individually definable over the original ground. -/
theorem residue_columns_named_gamma_tuple_separation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n m : ℕ} (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop)
    (hR : mixedGammaTupleDefinable B R)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (a b : Fin n → M) (ha : ∀ i, a i ∈ D i) (hb : ∀ i, b i ∈ D i)
    (hne : ∃ γ, ¬ (R a γ ↔ R b γ)) :
    ∃ γ, (∀ i, GammaDefinableClosureAtBase B (γ i)) ∧ ¬ (R a γ ↔ R b γ) := by
  let C : Base (M := M) := ⟨(B.real ∪ Set.range a) ∪ Set.range b,B.gamma⟩
  have hBC : B.real ⊆ C.real := fun _ h => Or.inl (Or.inl h)
  have haC : B.real ∪ Set.range a ⊆ C.real := Set.subset_union_left
  have hbC : B.real ∪ Set.range b ⊆ C.real := by
    rintro t (ht | ht)
    · exact hBC ht
    · exact Or.inr ht
  have hRa : FullGammaSyntax.Definable (integrationGammaBase C) (R a) :=
    FullBaseAtomicity.OverBase.mono (hR.column a) haC Set.Subset.rfl
  have hRb : FullGammaSyntax.Definable (integrationGammaBase C) (R b) :=
    FullBaseAtomicity.OverBase.mono (hR.column b) hbC Set.Subset.rfl
  have hDiff := (hRa.iff hRb).not
  obtain ⟨δ,hδ,hδ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  have hδC : FullGammaSyntax.Scalar (integrationGammaBase C) {δ} :=
    FullBaseAtomicity.OverBase.mono hδ hBC Set.Subset.rfl
  obtain ⟨γ,hγ,hγdef⟩ := fullGammaTuple_definable_point h00 δ hδC hδ1
    {γ | ¬ (R a γ ↔ R b γ)} hDiff hne
  refine ⟨γ,?_,hγ⟩
  intro i
  have hγC := nativeGamma_named_of_full_scalar C (γ i) (hγdef i)
  exact residue_pair_gamma_algebraic_elimination hκ hs h00 B hsmall D D hD hD hvalues hvalues
    a ha b hb (γ i) ((gamma_algebraic_iff_definable_base C (γ i)).mpr hγC)
end DiamondIntegral.Section3
