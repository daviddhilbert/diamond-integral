import «section 3».MixedGammaTupleLogic
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




theorem mixedGammaTupleDefinable.column_difference {B : Base (M := M)} {n m : ℕ}
    {R : (Fin n → M) → (Fin m → Values.Gamma (M := M)) → Prop}
    (hR : mixedGammaTupleDefinable B R) :
    FullRawDefinable (integrationGammaBase B) (fun z : Fin n ⊕ Fin n → M =>
      ∃ γ, ¬ (R (z ∘ Sum.inl) γ ↔ R (z ∘ Sum.inr) γ)) := by
  let pa : Fin n ⊕ Fin m → (Fin n ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let pb : Fin n ⊕ Fin m → (Fin n ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (fun i => .inl (.inr i)) Sum.inr
  have hh := ((FullRawDefinable.reindex hR pa).iff (FullRawDefinable.reindex hR pb)).not.exists_block
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change (∃ c : Fin m → M,
    ¬ ((GammaSyntax.Proper c ∧ R (z ∘ Sum.inl) (GammaSyntax.decode c)) ↔
       (GammaSyntax.Proper c ∧ R (z ∘ Sum.inr) (GammaSyntax.decode c)))) ↔
    ∃ γ, ¬ (R (z ∘ Sum.inl) γ ↔ R (z ∘ Sum.inr) γ)
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨GammaSyntax.decode c,?_⟩
    intro he
    exact hc (and_congr Iff.rfl he)
  · rintro ⟨γ,hγ⟩
    let c := representatives γ
    have hp : GammaSyntax.Proper (rawTuple c) := rawTuple_proper c
    have he : GammaSyntax.decode (rawTuple c) = γ := by
      funext i
      exact (codeValue_raw _).trans (congrFun (representatives_values γ) i)
    refine ⟨rawTuple c,?_⟩
    simpa only [hp,true_and,he] using hγ
end DiamondIntegral.Section3
