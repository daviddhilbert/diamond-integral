import «section 3».FullGammaCodeLogic
import «section 3».IntegrationGammaParameters
import IntegrationSection3ACVF.AdjoinGamma
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaUniversalCodePredicate {α : Type}
    (R : ParameterPresentation.Name (M := M) → Set (α → M))
    (z : Fin 1 ⊕ α → Values.Gamma (M := M)) : Prop :=
  ∀ c : α → M, GammaSyntax.Proper c → GammaSyntax.decode c = z ∘ Sum.inr → c ∈ R (Sum.inr (z (.inl 0)))

theorem gammaUniversalCodePredicate_definable {α : Type} [Finite α]
    (B : FullBaseAtomicity.Base (M := M)) (R : ParameterPresentation.Name (M := M) → Set (α → M))
    (hR : FullBaseAtomicity.OverBase B
      (ImaginaryParameters.vectorPullback (@ParameterPresentation.presentation M inferInstance inferInstance) R)) :
    FullGammaSyntax.Definable B (gammaUniversalCodePredicate R) := by
  have hr := AdjoinGamma.restrict_vector B R hR
  let e : Fin 1 ⊕ α → (Fin 1 ⊕ α) ⊕ α := Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hr' := FullRawDefinable.reindex hr e
  have hs := FullRawDefinable.forall_finite (fun i : α =>
    fullRaw_sameScalar B (Sum.inr i : (Fin 1 ⊕ α) ⊕ α) (Sum.inl (Sum.inr i)))
  have hh := (hs.imp hr').forall_block
  have hp : FullRawDefinable B (fun z : Fin 1 ⊕ α → M => GammaSyntax.Proper z) := FullGammaSyntax.proper_definable B
  apply FullBaseAtomicity.OverBase.congr (hp.and hh)
  intro z
  change (GammaSyntax.Proper z ∧ ∀ c : α → M,
    (∀ i, SameScalar (c i) (z (.inr i))) →
      (NonzeroRV (z (.inl 0)) ∧ c ∈ R (Sum.inr (codeValue (z (.inl 0)))))) ↔
    (GammaSyntax.Proper z ∧ gammaUniversalCodePredicate R (GammaSyntax.decode z))
  constructor
  · rintro ⟨hz,hh⟩
    refine ⟨hz,?_⟩
    intro c hc he
    have hsame := (gammaCode_same_iff c (z ∘ Sum.inr) (fun i => hz (.inr i))).mpr ⟨hc,he⟩
    exact (hh c hsame).2
  · rintro ⟨hz,hq⟩
    refine ⟨hz,?_⟩
    intro c hsame
    obtain ⟨hc,he⟩ := (gammaCode_same_iff c (z ∘ Sum.inr) (fun i => hz (.inr i))).mp hsame
    exact ⟨hz (.inl 0),hq c hc he⟩

/-- A named Gamma parameter can be replaced by a free Gamma variable
while retaining a complete, invariant code predicate over the old base. -/
theorem fullGamma_adjoin_abstraction {α : Type} [Finite α]
    (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (P : (α → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable (integrationGammaBase (Section2.adjoinGamma B γ)) P) :
    ∃ Q : ((Fin 1 ⊕ α) → Values.Gamma (M := M)) → Prop,
      FullGammaSyntax.Definable (integrationGammaBase B) Q ∧
      ∀ x, Q (Sum.elim (fun _ : Fin 1 => γ) x) ↔ P x := by
  change FullBaseAtomicity.OverBase (integrationGammaBase (Section2.adjoinGamma B γ))
    {c : α → M | GammaSyntax.Proper c ∧ P (GammaSyntax.decode c)} at hP
  rw [integrationGammaBase_adjoin] at hP
  obtain ⟨R,hR,hRA⟩ := (FullBaseAtomicity.OverBase.adjoin_iff (Sum.inr γ) _).mp hP
  refine ⟨gammaUniversalCodePredicate R,gammaUniversalCodePredicate_definable _ R hR,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨c,hc,he⟩ := gammaTuple_has_full_code x
    have hh := hx c hc he
    change c ∈ R (Sum.inr γ) at hh
    rw [hRA] at hh
    exact he ▸ hh.2
  · intro hx c hc he
    change GammaSyntax.decode c = x at he
    change c ∈ R (Sum.inr γ)
    rw [hRA]
    exact ⟨hc,he.symm ▸ hx⟩
end DiamondIntegral.Section3
