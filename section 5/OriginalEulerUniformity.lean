import «section 5».OriginalEulerValidityLoci
import «section 5».EulerCertificateCongruence
import IntegrationSection6.GammaWitnessUniformity

/-! Genuine original-base compactness selects a finite catalog of whole
Euler certificates, retaining every tree shape and computed integer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}

theorem original_euler_certificate_for_fixed_source
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (D : GammaDomainFormula B p n sp) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (hD : (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B D)).Realize
        (predicateParameterValues B z)) :
    ∃ C : OriginalEulerCertificate B sp n,
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z) := by
  let G := nativeGammaRelationSyntax hc
  let φ := gammaDomainSyntax hc B D
  let v := predicateParameterValues B z
  let X := quotientFormulaDomain φ v (codeValue (M := M))
  have hrep : gammaFormulaRepresents φ v X :=
    quotientFormulaDomain_full_preimage G.proper G.equal φ v NonzeroRV codeValue
      G.proper_realize G.equal_realize hD
  have hX : GammaDefinable ⟨B.real ∪ Set.range z, B.gamma⟩ X := by
    change DefinableOverBase _ (fun _ : Fin n => .rv)
      {x | Proper x ∧ (fun i => codeValue (M := M) (x i)) ∈ X}
    convert gammaDomainSyntax_row_definable hc B D z using 1
    ext x
    exact (hrep x).symm
  obtain ⟨E, C, hE, hv, _⟩ := original_euler_certificate_exists hc h00 hκ hs B hr hγ sp z hz X hX
  refine ⟨C, ?_⟩
  have hrow (x : Fin n → M) :
      (gammaDomainSyntax hc B E).Realize (Sum.elim v x) ↔ φ.Realize (Sum.elim v x) :=
    (hE x).trans (hrep x).symm
  have hh := hv
  simp only [EulerFormulaCertificate.validity, Formula.realize_inf] at hh ⊢
  exact ⟨hh.1, (finitePartitionValidity_congr _ _ _ _ v v hrow (fun _ _ => Iff.rfl)).mp hh.2⟩

theorem original_euler_finite_catalog
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (D : GammaDomainFormula B p n sp)
    (hD : ∀ z ∈ A, (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B D)).Realize
        (predicateParameterValues B z)) :
    ∃ J : Finset (OriginalEulerCertificate B sp n), ∀ z ∈ A, ∃ C ∈ J,
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z) := by
  let valid (C : OriginalEulerCertificate B sp n) := {z : Fin p → M |
    (∀ i, sortEval (sp i) (z i)) ∧
      ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z)}
  obtain ⟨J, hJ⟩ := gamma_finite_witnesses hκ hs hr hγ sp A hA valid
    (fun C => C.validity_definable hc D) (by
      intro z hz
      obtain ⟨C, hv⟩ := original_euler_certificate_for_fixed_source hc h00 hκ hs hr hγ D z
        (hA.proper z hz) (hD z hz)
      exact ⟨C, hA.proper z hz, hv⟩)
  refine ⟨J, ?_⟩
  intro z hz
  obtain ⟨C, hC, hv⟩ := hJ z hz
  exact ⟨C, hC, hv.2⟩

end DiamondIntegral.Section5
