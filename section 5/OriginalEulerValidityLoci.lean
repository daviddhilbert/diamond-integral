import «section 5».OriginalCylindricalStepValidity
import «section 5».OriginalQuotientValidity
import «section 5».OriginalFinitePartitionValidity
import «section 5».OriginalEulerCertificateExistence

/-! Validity of an entire native Euler certificate is definable over the
original real/Gamma base, before choosing any finite catalog. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}

theorem OriginalGammaCellTree.validity_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : OriginalGammaCellTree B sp n) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less).Realize
          (predicateParameterValues B z)} := by
  induction C with
  | base =>
    convert real_definableOverBase B sp (sortedUniverse sp) (sortedUniverse_definable B.real sp) using 1
    ext z
    simp only [OriginalGammaCellTree.syntax, CylindricalFormulaTree.validity,
      setEqualityValidityFormula_realize, and_true, sortedUniverse, Set.mem_ofPred_eq]
  | @step n C k D ih =>
    have h := (ih.inter (original_quotient_domain_validity_definable hc D)).inter
      (original_cylindrical_step_validity_definable hc k C.domainFormula D)
    convert h using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, OriginalGammaCellTree.syntax,
      CylindricalFormulaTree.validity, Formula.realize_inf]
    have he (hz : ∀ i, sortEval (sp i) (z i)) :
        (cylindricalStepValidityFormula k (nativeGammaRelationSyntax hc).proper
          (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
          (C.syntax hc).domain (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z) ↔
        (cylindricalStepValidityFormula k (nativeGammaRelationSyntax hc).proper
          (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
          (gammaDomainSyntax hc B C.domainFormula) (gammaDomainSyntax hc B D)).Realize
            (predicateParameterValues B z) :=
      cylindricalStepValidity_congr _ _ _ _ _ _ _ _ _ _
        (fun x => (C.domainFormula_realize hc z hz x).trans
          (gammaDomainSyntax_realize hc B C.domainFormula z x).symm) (fun _ => Iff.rfl)
    constructor
    · rintro ⟨hz, ⟨hchild, hquot⟩, hstep⟩
      exact ⟨⟨⟨hz, hchild⟩, hz, hquot⟩, hz, (he hz).mp hstep⟩
    · rintro ⟨⟨⟨hz, hchild⟩, _, hquot⟩, _, hstep⟩
      exact ⟨hz, ⟨hchild, hquot⟩, (he hz).mpr hstep⟩

theorem OriginalEulerCertificate.validity_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : OriginalEulerCertificate B sp n) (D : GammaDomainFormula B p n sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z)} := by
  have hcells : OriginalSortedPredicate B sp (fun z => ∀ i,
      (((C.cells i).syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less).Realize
          (predicateParameterValues B z)) :=
    OriginalSortedPredicate.finite_all (fun i => (C.cells i).validity_definable hc)
  have hpart := original_finite_partition_validity_definable B sp (fun _ : Fin n => .rv)
    D.val (fun i : Fin C.size => (C.cells i).domainFormula.val) D.property
    (fun i => (C.cells i).domainFormula.property)
  have h := hcells.inter hpart
  convert h using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, OriginalEulerCertificate.syntax,
    EulerFormulaCertificate.validity, Formula.realize_inf, finiteWitnessValidityFormula_realize]
  have he (hz : ∀ i, sortEval (sp i) (z i)) :
      (finitePartitionValidityFormula (gammaDomainSyntax hc B D)
        (fun i => ((C.cells i).syntax hc).domain)).Realize (predicateParameterValues B z) ↔
      (∀ x : Fin n → M, Fin.append z x ∈ D.val ↔
        ∃ i, Fin.append z x ∈ (C.cells i).domainFormula.val) ∧
      ∀ i j, i ≠ j → ∀ x : Fin n → M,
        ¬ (Fin.append z x ∈ (C.cells i).domainFormula.val ∧
          Fin.append z x ∈ (C.cells j).domainFormula.val) := by
    rw [finitePartitionValidityFormula_realize]
    simp_rw [gammaDomainSyntax_realize, OriginalGammaCellTree.domainFormula_realize hc _ z hz]
  constructor
  · rintro ⟨hz, hcell, hpartition⟩
    exact ⟨⟨hz, hcell⟩, hz, (he hz).mp hpartition⟩
  · rintro ⟨⟨hz, hcell⟩, _, hpartition⟩
    exact ⟨hz, hcell, (he hz).mpr hpartition⟩

end DiamondIntegral.Section5
