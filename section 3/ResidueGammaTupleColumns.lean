import «section 3».ResidueGammaTupleSeparation
import «section 3».MixedGammaTupleDifferences
import «section 3».GammaFullRawCommonNames
import «section 3».DefinableTestColumns
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



/-- ACVF residue/Gamma orthogonality in arbitrary finite tuple arities:
a mixed family on a finite-value residue domain has finitely many columns. -/
theorem residue_gamma_tuple_finite_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n m : ℕ} (R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop)
    (hR : mixedGammaTupleDefinable B R) (hsort : ∀ a γ, R a γ → ∀ i, iRV (a i))
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i) :
    (relationColumn (fun γ a => R a γ) '' A).Finite := by
  let U := fun γ a => R a γ
  let S := commonRealNames B
  let T : Set (Fin m → Values.Gamma (M := M)) := {γ | ∀ i, GammaDefinableClosureAtBase B (γ i)}
  let Bad : Set (Fin n ⊕ Fin n → M) := {z | z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A ∧
    relationColumn U (z ∘ Sum.inl) ≠ relationColumn U (z ∘ Sum.inr)}
  have hBadFull : FullRawDefinable (integrationGammaBase B) (fun z => z ∈ Bad) := by
    have hd := hR.column_difference
    have hh := ((FullRawDefinable.reindex (integrationGammaDefinable hA) (Sum.inl : Fin n → Fin n ⊕ Fin n)).and
      (FullRawDefinable.reindex (integrationGammaDefinable hA) (Sum.inr : Fin n → Fin n ⊕ Fin n))).and hd
    apply FullBaseAtomicity.OverBase.congr hh
    intro z
    change ((z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A) ∧ ∃ γ, ¬ (R (z ∘ Sum.inl) γ ↔ R (z ∘ Sum.inr) γ)) ↔
      (z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A ∧ relationColumn U (z ∘ Sum.inl) ≠ relationColumn U (z ∘ Sum.inr))
    have he : (∃ γ, ¬ (R (z ∘ Sum.inl) γ ↔ R (z ∘ Sum.inr) γ)) ↔
        relationColumn U (z ∘ Sum.inl) ≠ relationColumn U (z ∘ Sum.inr) := by
      constructor
      · rintro ⟨γ,hγ⟩ he
        exact hγ (Set.ext_iff.mp he γ)
      · intro hn
        by_contra hall
        push_neg at hall
        exact hn (Set.ext hall)
    rw [he]
    tauto
  have hBad : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin n) Bad :=
    gammaFullRaw_common_names B (fun z => z ∈ Bad) hBadFull (by
      intro z hz i
      cases i with
      | inl i => simpa only [sortEval,iRV,Function.comp_apply] using hA.proper (z ∘ Sum.inl) hz.1 i
      | inr i => simpa only [sortEval,iRV,Function.comp_apply] using hA.proper (z ∘ Sum.inr) hz.2.1 i)
  have htest : ∀ γ ∈ T, @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n) {a | U γ a} := by
    intro γ hγ
    exact gammaFullRaw_common_names B (fun a => R a γ)
      (hR.fibre γ (fun i => integrationGammaDefinable (hγ i))) (fun a ha => hsort a γ ha)
  have hsep : ∀ a ∈ A, ∀ b ∈ A, relationColumn U a ≠ relationColumn U b →
      ∃ γ ∈ T, ¬ (U γ a ↔ U γ b) := by
    intro a ha b hb hn
    have hne : ∃ γ, ¬ (R a γ ↔ R b γ) := by
      by_contra hh
      push_neg at hh
      exact hn (Set.ext hh)
    obtain ⟨γ,hγ,hneq⟩ := residue_columns_named_gamma_tuple_separation hκ hs h00 B hsmall hΓ R hR
      D hD hvalues a b (hsub a ha) (hsub b hb) hne
    exact ⟨γ,hγ,hneq⟩
  have hsmallS : Cardinal.mk S < κ := commonRealNames_small hκ B hsmall hγsmall
  have hsN := hs.normalize
  have hf : (relationColumn U '' A).Finite := by
    letI := CanonicalStructure.normalize (M := M)
    exact finite_columns_of_definable_separating_tests hsN S hsmallS U A hBad T htest hsep
  exact hf
end DiamondIntegral.Section3
