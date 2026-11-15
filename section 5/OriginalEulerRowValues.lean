import «section 5».OriginalEulerUniformity

/-! Whole original Euler certificates compute the actual integral of a
fixed Gamma-domain row over its displayed parameter base. -/
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

def originalGammaSourceValid (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) : Prop :=
  (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
    (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z)

def originalGammaSourceRow (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) : Set (Fin n → Values.Gamma (M := M)) :=
  quotientFormulaDomain (gammaDomainSyntax hc B D) (predicateParameterValues B z) (codeValue (M := M))

theorem originalGammaSourceRow_represents (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) (hD : originalGammaSourceValid hc D z) :
    gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z)
      (originalGammaSourceRow hc D z) :=
  quotientFormulaDomain_full_preimage (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
    (gammaDomainSyntax hc B D) (predicateParameterValues B z) NonzeroRV codeValue
    (nativeGammaRelationSyntax hc).proper_realize (nativeGammaRelationSyntax hc).equal_realize hD

theorem originalGammaSourceRow_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) (hD : originalGammaSourceValid hc D z) :
    GammaDefinable ⟨B.real ∪ Set.range z, B.gamma⟩ (originalGammaSourceRow hc D z) := by
  change DefinableOverBase _ (fun _ : Fin n => .rv)
    {x | Proper x ∧ (fun i => codeValue (M := M) (x i)) ∈ originalGammaSourceRow hc D z}
  convert gammaDomainSyntax_row_definable hc B D z using 1
  ext x
  exact (originalGammaSourceRow_represents hc D z hD x).symm

def originalGammaRowEulerValue (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) (kind : EulerKind) : ℤ :=
  if hD : originalGammaSourceValid hc D z then
    GammaIteratedIntegral.integrateAll h00 hκ hs ⟨B.real ∪ Set.range z, B.gamma⟩
      (small_union_range_carrier hκ B.real hr z) hγ kind n
      (GammaIndicators.indicatorFamily _ (originalGammaSourceRow hc D z) (originalGammaSourceRow_definable hc D z hD))
  else 0

def OriginalEulerCertificate.ValidFor (hc : CanonicalStructure.IsCanonical (M := M))
    (C : OriginalEulerCertificate B sp n) (D : GammaDomainFormula B p n sp) (z : Fin p → M) : Prop :=
  ((C.syntax hc).validity (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal
    (nativeGammaRelationSyntax hc).less (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z)

theorem OriginalEulerCertificate.validFor_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : OriginalEulerCertificate B sp n) (D : GammaDomainFormula B p n sp) :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧ C.ValidFor hc D z} :=
  C.validity_definable hc D

theorem OriginalEulerCertificate.originalGammaRowEulerValue
    (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (C : OriginalEulerCertificate B sp n) (D : GammaDomainFormula B p n sp) (z : Fin p → M)
    (hv : C.ValidFor hc D z) (kind : EulerKind) :
    originalGammaRowEulerValue hc h00 hκ hs hr hγ D z kind = (C.syntax hc).eulerValue kind := by
  let G := nativeGammaRelationSyntax hc
  have hD : originalGammaSourceValid hc D z :=
    (C.syntax hc).source_quotient_validity G.proper G.equal G.less _ _ hv
  unfold DiamondIntegral.Section5.originalGammaRowEulerValue
  rw [dif_pos hD]
  exact (C.syntax hc).integral_eq G.proper G.equal G.less G.proper_realize G.equal_realize G.less_realize
    h00 hκ hs ⟨B.real ∪ Set.range z, B.gamma⟩ (small_union_range_carrier hκ B.real hr z) hγ
    (predicateParameterValues B z) (gammaDomainSyntax hc B D) (originalGammaSourceRow hc D z)
    (originalGammaSourceRow_definable hc D z hD)
    (fun x hx => (originalGammaSourceRow_represents hc D z hD x).trans (and_iff_right hx)) hv
    (fun i => (C.cells i).raw_definable hc z) kind

end DiamondIntegral.Section5
