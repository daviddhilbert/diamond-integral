import «section 5».RESLayoutPredicates
import «section 5».OriginalEulerCatalogPreparation
import «section 5».FiniteMixedGraphPreparation

/-! One genuine original-base special bijection prepares a finite catalog
of entire native equality witnesses with mixed VF/RV base coordinates. -/
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


theorem prepare_joint_res_euler_catalog (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p q a b n : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : RESSetSchema B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (G : RESSetSchema B (p+q) b (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (J : Finset (RESLayoutStabilizationSchema F G))
    (K : Finset (OriginalEulerCertificate B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) n))
    (D : GammaDomainFormula B (p+q) n (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
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
      (∀ E ∈ K, ∀ (x : C) (v : Fin q → M),
        ((E.syntax hc).validity (nativeGammaRelationSyntax hc).proper
          (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
          (gammaDomainSyntax hc B D)).Realize
            (predicateParameterValues B (Fin.append (rawVFParameter (T.inverseMap x).val) v)) ↔
        (((E.recode (mixedPreparedParameterRecode T hT q)).syntax hc).validity
          (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
          (nativeGammaRelationSyntax hc).less
          (gammaDomainSyntax hc B ((mixedPreparedParameterRecode T hT q).domain D))).Realize
            (predicateParameterValues B (Fin.append (rawPreparedKey x.val) v))) := by
  let I := ((W : J) × Fin W.val.domainPredicates.length) ⊕
    Option ((E : K) × (i : Fin E.val.size) × Fin ((E.val.cells i).predicates.length))
  let H := (W : J) × Fin W.val.graphPredicates.length
  let arity : I → ℕ
    | .inl i => (i.1.val.domainPredicates.get i.2).1
    | .inr none => n
    | .inr (some i) => (((i.1.val.cells i.2.1).predicates).get i.2.2).1
  let domain : (i : I) → GammaDomainFormula B (p+q) (arity i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | .inl i => (i.1.val.domainPredicates.get i.2).2
    | .inr none => D
    | .inr (some i) => (((i.1.val.cells i.2.1).predicates).get i.2.2).2
  let leftArity (i : H) := (i.1.val.graphPredicates.get i.2).1
  let rightArity (i : H) := (i.1.val.graphPredicates.get i.2).2.1
  let graph (i : H) := (i.1.val.graphPredicates.get i.2).2.2
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hD, hH⟩ :=
    prepare_finite_mixed_original_base_RV_graphs hκ hs h00 B hsmall A hA arity leftArity rightArity domain graph
  refine ⟨R, hSR, hBR, l, C, T, hT, hC, ?_, ?_⟩
  · intro W hW x v hv
    have hrow : W.RowAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
      apply (W.rowAgreement_iff_predicates _ _ _).mpr
      constructor
      · intro D hDmem
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hDmem
        exact hD (.inl ⟨⟨W, hW⟩, i⟩) x v
      · intro H hHmem
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hHmem
        exact hH ⟨⟨W, hW⟩, i⟩ x v
    refine ⟨hrow, W.recode_valid_iff hc _ _ _ ?_ ?_ hrow⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left, rawVFParameter] using ((T.inverseMap x).val.1 j).property
      · simpa only [Fin.append_right, sortEval, iRV] using hv j
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left, sortEval, iRV, rawPreparedKey] using ((flatKey x.val).2 j).property
      · simpa only [Fin.append_right, sortEval, iRV] using hv j
  · intro E hE x v
    let reindex := mixedPreparedParameterRecode T hT q
    have hsource : reindex.DomainAgreement D
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) :=
      hD (.inr none) x v
    have hforest : E.RowAgreement reindex
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
      intro i
      apply ((E.cells i).rowAgreement_iff_predicates reindex _ _).mpr
      intro Q hQ
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hQ
      exact hD (.inr (some ⟨⟨E, hE⟩, i, j⟩)) x v
    exact E.recode_validity_iff hc reindex D _ _ hforest hsource _ _ _

end DiamondIntegral.Section5
