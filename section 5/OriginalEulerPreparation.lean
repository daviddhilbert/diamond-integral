import «section 5».OriginalEulerRecoding
import «section 5».FiniteFormulaPreparation
import Mathlib.Data.Fintype.Sigma

/-! One actual special bijection prepares the source and every primitive
predicate of an entire finite original Euler certificate. Validity descends
together with all its discrete shapes and computed Euler integers. -/
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

theorem prepare_original_euler_certificate (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p n : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (C : OriginalEulerCertificate B (fun _ : Fin p => .vf) n)
    (D : GammaDomainFormula B p n (fun _ => .vf)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ F : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) F,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier F) ∧
      ∀ x : F,
        ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
          (nativeGammaRelationSyntax hc).less (gammaDomainSyntax hc B D)).Realize
            (predicateParameterValues B (rawVFParameter (T.inverseMap x).val)) ↔
        (((C.recode (GammaParameterRecode.prepared T hT)).syntax hc).validity
          (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
          (nativeGammaRelationSyntax hc).less
          (gammaDomainSyntax hc B ((GammaParameterRecode.prepared T hT).domain D))).Realize
            (predicateParameterValues B (rawPreparedKey x.val)) := by
  let I := Option ((i : Fin C.size) × Fin ((C.cells i).predicates.length))
  let arity : I → ℕ
    | none => n
    | some i => ((C.cells i.1).predicates.get i.2).1
  let domain : (i : I) → GammaDomainFormula B p (arity i) (fun _ => .vf)
    | none => D
    | some i => ((C.cells i.1).predicates.get i.2).2
  obtain ⟨R, hSR, hBR, l, F, T, hT, hF, hrows⟩ :=
    prepare_finite_original_base_RV_predicates hκ hs h00 B hsmall A hA arity domain
  refine ⟨R, hSR, hBR, l, F, T, hT, hF, ?_⟩
  intro x
  let reindex := GammaParameterRecode.prepared T hT
  have hD : reindex.DomainAgreement D (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    hrows none x
  have hC : C.RowAgreement reindex (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
    intro i
    apply ((C.cells i).rowAgreement_iff_predicates reindex _ _).mpr
    intro E hE
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hE
    exact hrows (some ⟨i, j⟩) x
  exact C.recode_validity_iff hc reindex D _ _ hC hD _ _ _

end DiamondIntegral.Section5
