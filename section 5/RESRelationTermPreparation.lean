import «section 5».RESRelationTermPredicates
import «section 5».FiniteGraphPreparation

/-! One genuine special bijection prepares a finite catalog of complete
native RES relation terms, retaining coefficient domains, full graphs and orientations. -/
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

theorem prepare_finite_res_relation_term_catalog (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (J : Finset (RESRelationTermSchema B p (fun _ => .vf))) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ P ∈ J, ∀ x : C,
        P.RowAgreement (GammaParameterRecode.prepared T hT)
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) ∧
        (P.Valid hc (rawVFParameter (T.inverseMap x).val) ↔
          (P.recode (GammaParameterRecode.prepared T hT)).Valid hc (rawPreparedKey x.val)) := by
  let I := (P : J) × Fin P.val.domainPredicates.length
  let K := (P : J) × Fin P.val.graphPredicates.length
  let arity (i : I) := (i.1.val.domainPredicates.get i.2).1
  let leftArity (i : K) := (i.1.val.graphPredicates.get i.2).1
  let rightArity (i : K) := (i.1.val.graphPredicates.get i.2).2.1
  let domain (i : I) := (i.1.val.domainPredicates.get i.2).2
  let graph (i : K) := (i.1.val.graphPredicates.get i.2).2.2
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hD, hH⟩ :=
    prepare_finite_original_base_RV_graphs hκ hs h00 B hsmall A hA arity leftArity rightArity domain graph
  refine ⟨R, hSR, hBR, l, C, T, hT, hC, ?_⟩
  intro P hP x
  have hrow : P.RowAgreement (GammaParameterRecode.prepared T hT)
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
    apply (P.rowAgreement_iff_predicates _ _ _).mpr
    constructor
    · intro D hDmem
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hDmem
      exact hD ⟨⟨P, hP⟩, i⟩ x
    · intro H hHmem
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hHmem
      exact hH ⟨⟨P, hP⟩, i⟩ x
  exact ⟨hrow, P.recode_valid_iff hc _ _ _
    (fun j => ((T.inverseMap x).val.1 j).property)
    (fun j => ((flatKey x.val).2 j).property) hrow⟩

end DiamondIntegral.Section5
