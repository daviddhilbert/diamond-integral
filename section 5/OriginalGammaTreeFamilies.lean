import «section 5».OriginalGammaFamilyRealizations
import «section 5».RVGammaCellFamilies
import «section 5».CylindricalStepQuotientFibres

/-! Entire valid original formula trees realize actual relative Gamma
cell families over the original RV parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def OriginalGammaCellTree.family
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (C : OriginalGammaCellTree B (fun _ : Fin p => .rv) n) :=
  originalGammaFamilyRealization X C.domainFormula

theorem OriginalGammaCellTree.family_row
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (C : OriginalGammaCellTree B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less).Realize
        (predicateParameterValues B (rvUnitValues x.val)))
    (x : X) (γ : Fin n → Values.Gamma (M := M)) :
    (x.val,γ) ∈ (C.family X).carrier ↔
      γ ∈ (C.syntax hc).gammaDomain (predicateParameterValues B (rvUnitValues x.val)) := by
  have hz : ∀ i, sortEval SortTag.rv (rvUnitValues x.val i) := fun i => (x.val i).val.property
  have hrelated : ∀ z : Fin n → M,
      (gammaDomainSyntax hc B C.domainFormula).Realize
        (Sum.elim (predicateParameterValues B (rvUnitValues x.val)) z) ↔
      (C.syntax hc).domain.Realize (Sum.elim (predicateParameterValues B (rvUnitValues x.val)) z) := by
    intro z
    exact (gammaDomainSyntax_realize hc B C.domainFormula _ z).trans (C.domainFormula_realize hc _ hz z).symm
  have hD : ∀ a : X, originalGammaSourceValid hc C.domainFormula (rvUnitValues a.val) := by
    intro a
    have hr (z : Fin n → M) := C.domainFormula_realize hc (rvUnitValues a.val)
      (fun i => (a.val i).val.property) z
    apply (quotientDomainValidity_congr (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
      _ _ _ _ (fun z => (gammaDomainSyntax_realize hc B C.domainFormula _ z).trans (hr z).symm)).mpr
    exact (C.syntax hc).domainValidity _ _ _ _ (hv a)
  refine (originalGammaFamilyRealization_row X C.domainFormula hD x γ).trans ?_
  change γ ∈ quotientFormulaDomain _ _ codeValue ↔ γ ∈ quotientFormulaDomain _ _ codeValue
  unfold quotientFormulaDomain
  constructor
  · rintro ⟨z,hz,hq⟩
    exact ⟨z,(hrelated z).mp hz,hq⟩
  · rintro ⟨z,hz,hq⟩
    exact ⟨z,(hrelated z).mpr hz,hq⟩

theorem OriginalGammaCellTree.family_is_cell
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (C : OriginalGammaCellTree B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less).Realize
        (predicateParameterValues B (rvUnitValues x.val))) :
    RVGammaCellFamily X (C.family X) (C.syntax hc).shape := by
  induction C with
  | base =>
    apply RVGammaCellFamily.base
    intro x γ
    constructor
    · exact originalGammaFamilyRealization_projection X _ x γ
    · intro hx
      apply (OriginalGammaCellTree.family_row X .base hv ⟨x,hx⟩ γ).mpr
      change γ ∈ quotientFormulaDomain ⊤ (predicateParameterValues B (rvUnitValues x)) codeValue
      obtain ⟨z,hz,hq⟩ := gamma_tuple_code_surjective γ
      exact ⟨z,by simp,hq⟩
  | @step n C shape D ih =>
    let G := nativeGammaRelationSyntax hc
    have hchild (x : X) : ((C.syntax hc).validity G.proper G.equal G.less).Realize
        (predicateParameterValues B (rvUnitValues x.val)) := by
      have h := hv x
      simp only [OriginalGammaCellTree.syntax,CylindricalFormulaTree.validity,Formula.realize_inf] at h
      exact h.1.1
    have hstep (x : X) :
        (∀ q ∈ ((OriginalGammaCellTree.step C shape D).syntax hc).gammaDomain
          (predicateParameterValues B (rvUnitValues x.val)),
          Fin.tail q ∈ (C.syntax hc).gammaDomain (predicateParameterValues B (rvUnitValues x.val))) ∧
        ∀ η ∈ (C.syntax hc).gammaDomain (predicateParameterValues B (rvUnitValues x.val)),
          shape.Describes (fun γ : Values.Gamma (M := M) => Fin.cons γ η ∈
            ((OriginalGammaCellTree.step C shape D).syntax hc).gammaDomain
              (predicateParameterValues B (rvUnitValues x.val))) := by
      have h := hv x
      simp only [OriginalGammaCellTree.syntax,CylindricalFormulaTree.validity,Formula.realize_inf] at h
      exact cylindrical_step_quotient_fibres G.proper G.equal G.less G.proper_realize G.equal_realize G.less_realize
        shape (C.syntax hc).domain (gammaDomainSyntax hc B D) _ _ _
        (quotientFormulaDomain_full_preimage G.proper G.equal (C.syntax hc).domain _ NonzeroRV codeValue
          G.proper_realize G.equal_realize ((C.syntax hc).domainValidity _ _ _ _ (hchild x)))
        (originalGammaSourceRow_represents hc D _ h.1.2) h.2
    apply RVGammaCellFamily.step (ih hchild) shape ((OriginalGammaCellTree.step C shape D).family X)
    · intro x γ ht
      have hx := originalGammaFamilyRealization_projection X D x γ ht
      have hq := ((OriginalGammaCellTree.step C shape D).family_row X hv ⟨x,hx⟩ γ).mp ht
      exact (C.family_row X hchild ⟨x,hx⟩ _).mpr ((hstep ⟨x,hx⟩).1 γ hq)
    · intro x η ht
      have hx := originalGammaFamilyRealization_projection X C.domainFormula x η ht
      have hη := (C.family_row X hchild ⟨x,hx⟩ η).mp ht
      obtain ⟨a,ha,hr⟩ := (hstep ⟨x,hx⟩).2 η hη
      exact ⟨a,ha,fun γ => ((OriginalGammaCellTree.step C shape D).family_row X hv ⟨x,hx⟩ _).trans (hr γ)⟩

end DiamondIntegral.Section5
