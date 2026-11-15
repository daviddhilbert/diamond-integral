import «section 5».GammaMixedPreparedRows

/-! One genuine original-base special bijection prepares finite families
with mixed VF/RV parameters. Original RV coordinates are carried unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem prepare_finite_mixed_original_base_RV_graphs {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p q : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    {ι η : Type} [Finite ι] [Finite η] (a : ι → ℕ) (b c : η → ℕ)
    (D : (i : ι) → GammaDomainFormula B (p+q) (a i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (H : (j : η) → GammaRelationFormula B (p+q) (b j) (c j)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      (∀ (i : ι) (x : C) (v : Fin q → M),
        (mixedPreparedParameterRecode T hT q).DomainAgreement (D i)
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v)) ∧
      (∀ (j : η) (x : C) (v : Fin q → M),
        (mixedPreparedParameterRecode T hT q).RelationAgreement (H j)
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v)) := by
  let arity : ι ⊕ η → ℕ := Sum.elim (fun i => q+a i) (fun j => q+(b j+c j))
  let domain : (i : ι ⊕ η) → GammaDomainFormula B p (arity i) (fun _ => .vf) :=
    Sum.rec (fun i => carryRVParameterDomain (D i))
      (fun j => carryRVParameterDomain (flattenGammaRelation (H j)))
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hrows⟩ :=
    prepare_finite_original_base_RV_predicates hκ hs h00 B hsmall A hA arity domain
  exact ⟨R, hSR, hBR, l, C, T, hT, hC,
    fun i x v => mixedPreparedParameterRecode_domain_agreement T hT (D i) x (hrows (Sum.inl i) x) v,
    fun j x v => mixedPreparedParameterRecode_relation_agreement T hT (H j) x (hrows (Sum.inr j) x) v⟩

end DiamondIntegral.Section5
