import «section 5».RVEvaluationEqualityPreparation

/-! Equality witnesses, representative labels and auxiliary base
predicates can be prepared together through one genuine special map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem prepare_rv_equality_with_extra_data (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ)
    {S : Set M} {p q a b : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A)) (kind : EulerKind)
    (D : GammaDomainFormula B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (E : GammaDomainFormula B (p+q) b (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (J : Finset (RVEvaluationEqualitySchema hc kind D E))
    {ι η : Type} [Fintype ι] [Fintype η] (c : ι → ℕ) (d e : η → ℕ)
    (extraDomain : (i : ι) → GammaDomainFormula B (p+q) (c i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (extraGraph : (i : η) → GammaRelationFormula B (p+q) (d i) (e i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      (∀ W ∈ J, ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        W.RowAgreement (mixedPreparedParameterRecode T hT q)
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
        (W.Valid hc (Fin.append (rawVFParameter (T.inverseMap x).val) v) ↔
          (W.recode (mixedPreparedParameterRecode T hT q)).Valid hc (Fin.append (rawPreparedKey x.val) v))) ∧
      (∀ i (x : C) (v : Fin q → M), (mixedPreparedParameterRecode T hT q).DomainAgreement (extraDomain i)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v)) ∧
      ∀ i (x : C) (v : Fin q → M), (mixedPreparedParameterRecode T hT q).RelationAgreement (extraGraph i)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
  let I := (W : J) × Fin W.val.domainPredicates.length
  let K := (W : J) × Fin W.val.graphPredicates.length
  let arity : I ⊕ ι → ℕ
    | .inl i => (i.1.val.domainPredicates.get i.2).1
    | .inr i => c i
  let leftArity : K ⊕ η → ℕ
    | .inl i => (i.1.val.graphPredicates.get i.2).1
    | .inr i => d i
  let rightArity : K ⊕ η → ℕ
    | .inl i => (i.1.val.graphPredicates.get i.2).2.1
    | .inr i => e i
  let domain : (i : I ⊕ ι) → GammaDomainFormula B (p+q) (arity i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | .inl i => (i.1.val.domainPredicates.get i.2).2
    | .inr i => extraDomain i
  let graph : (i : K ⊕ η) → GammaRelationFormula B (p+q) (leftArity i) (rightArity i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | .inl i => (i.1.val.graphPredicates.get i.2).2.2
    | .inr i => extraGraph i
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hD,hH⟩ :=
    prepare_finite_mixed_original_base_RV_graphs hκ hs h00 B hr A hA arity leftArity rightArity domain graph
  refine ⟨R,hSR,hBR,l,C,T,hT,hC,?_,?_,?_⟩
  · intro W hW x v hv
    have hrow : W.RowAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
      apply (W.rowAgreement_iff_predicates _ _ _).mpr
      constructor
      · intro D hDmem
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hDmem
        exact hD (.inl ⟨⟨W,hW⟩,i⟩) x v
      · intro H hHmem
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hHmem
        exact hH (.inl ⟨⟨W,hW⟩,i⟩) x v
    refine ⟨hrow,W.recode_valid_iff _ _ _ ?_ ?_ hrow⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left,rawVFParameter] using ((T.inverseMap x).val.1 j).property
      · simpa only [Fin.append_right,sortEval,iRV] using hv j
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left,sortEval,iRV,rawPreparedKey] using ((flatKey x.val).2 j).property
      · simpa only [Fin.append_right,sortEval,iRV] using hv j
  · exact fun i x v => hD (.inr i) x v
  · exact fun i x v => hH (.inr i) x v

end DiamondIntegral.Section5
