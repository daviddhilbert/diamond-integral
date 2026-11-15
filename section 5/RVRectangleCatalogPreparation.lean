import «section 5».RVRectanglePredicateLists
import «section 5».FiniteMixedGraphPreparation

/-! One genuine special bijection prepares an entire finite catalog of
RV rectangle packages, including every Euler node and every map graph. -/
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

theorem prepare_rv_rectangle_catalog (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {S : Set M} {p q a : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (D : GammaDomainFormula B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (J : Finset (RVRectangleDecompositionSchema D)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ W ∈ J, ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        (W.Valid hc (Fin.append (rawVFParameter (T.inverseMap x).val) v) ↔
          (W.recode (mixedPreparedParameterRecode T hT q)).Valid hc (Fin.append (rawPreparedKey x.val) v)) := by
  let I := Option ((W : J) × (i : Fin W.val.size) × Fin ((W.val.cells i).domainPredicates.length))
  let H := (W : J) × Fin W.val.size
  let arity : I → ℕ
    | none => a
    | some i => (((i.1.val.cells i.2.1).domainPredicates).get i.2.2).1
  let domain : (i : I) → GammaDomainFormula B (p+q) (arity i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | none => D
    | some i => (((i.1.val.cells i.2.1).domainPredicates).get i.2.2).2
  let leftArity (_ : H) := a
  let rightArity (i : H) := (i.1.val.cells i.2).residueArity + (i.1.val.cells i.2).freeArity
  let graph (i : H) := (i.1.val.cells i.2).graph
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hD,hG⟩ :=
    prepare_finite_mixed_original_base_RV_graphs hκ hs h00 B hsmall A hA arity leftArity rightArity domain graph
  refine ⟨R,hSR,hBR,l,C,T,hT,hC,?_⟩
  intro W hW x v hv
  let recode := mixedPreparedParameterRecode T hT q
  apply W.recode_valid_iff hc recode _ _
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,rawVFParameter] using ((T.inverseMap x).val.1 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,sortEval,iRV,rawPreparedKey] using ((flatKey x.val).2 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j
  · exact hD none x v
  · intro i
    apply ((W.cells i).rowAgreement_iff_predicates recode _ _).mpr
    refine ⟨?_,hG ⟨⟨W,hW⟩,i⟩ x v⟩
    intro Q hQ
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hQ
    exact hD (some ⟨⟨W,hW⟩,i,j⟩) x v

end DiamondIntegral.Section5
