import «section 5».RESLayoutPredicates
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

theorem prepare_finite_res_layout_catalog (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p q a b : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : RESSetSchema B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (G : RESSetSchema B (p+q) b (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (J : Finset (RESLayoutStabilizationSchema F G)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ W ∈ J, ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        W.RowAgreement (mixedPreparedParameterRecode T hT q)
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
        (W.Valid hc (Fin.append (rawVFParameter (T.inverseMap x).val) v) ↔
          (W.recode (mixedPreparedParameterRecode T hT q)).Valid hc (Fin.append (rawPreparedKey x.val) v)) := by
  let I := (W : J) × Fin W.val.domainPredicates.length
  let K := (W : J) × Fin W.val.graphPredicates.length
  let arity (i : I) := (i.1.val.domainPredicates.get i.2).1
  let leftArity (i : K) := (i.1.val.graphPredicates.get i.2).1
  let rightArity (i : K) := (i.1.val.graphPredicates.get i.2).2.1
  let domain (i : I) := (i.1.val.domainPredicates.get i.2).2
  let graph (i : K) := (i.1.val.graphPredicates.get i.2).2.2
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hD, hH⟩ :=
    prepare_finite_mixed_original_base_RV_graphs hκ hs h00 B hsmall A hA arity leftArity rightArity domain graph
  refine ⟨R, hSR, hBR, l, C, T, hT, hC, ?_⟩
  intro W hW x v hv
  have hrow : W.RowAgreement (mixedPreparedParameterRecode T hT q)
      (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
    apply (W.rowAgreement_iff_predicates _ _ _).mpr
    constructor
    · intro D hDmem
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hDmem
      exact hD ⟨⟨W, hW⟩, i⟩ x v
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

end DiamondIntegral.Section5
