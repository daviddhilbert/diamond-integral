import «section 5».OriginalGammaTreeFamilies
import «section 5».RVGammaFamilySchemata

/-! A valid whole Euler certificate partitions the entire actual mixed
family, uniformly over the original RV base. -/
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

theorem OriginalEulerCertificate.family_partition
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier)
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, C.ValidFor hc (rvGammaFamilySchema T) (rvUnitValues x.val)) :
    (∀ i j, i ≠ j → Disjoint ((C.cells i).family X).carrier ((C.cells j).family X).carrier) ∧
      ∀ x γ, (x,γ) ∈ T.carrier ↔ ∃ i, (x,γ) ∈ ((C.cells i).family X).carrier := by
  let G := nativeGammaRelationSyntax hc
  have hcells (x : X) (i : Fin C.size) :
      (((C.cells i).syntax hc).validity G.proper G.equal G.less).Realize
        (predicateParameterValues B (rvUnitValues x.val)) := by
    have h := hv x
    simp only [OriginalEulerCertificate.ValidFor,EulerFormulaCertificate.validity,
      Formula.realize_inf,finiteWitnessValidityFormula_realize] at h
    exact h.1 i
  have hparts (x : X) := (finitePartitionValidityFormula_realize
    (gammaDomainSyntax hc B (rvGammaFamilySchema T)) (fun i => ((C.cells i).syntax hc).domain)
    (predicateParameterValues B (rvUnitValues x.val))).mp (by
      have h := hv x
      simp only [OriginalEulerCertificate.ValidFor,EulerFormulaCertificate.validity,Formula.realize_inf] at h
      exact h.2)
  have hmem (x : X) (i : Fin C.size) (γ : Fin n → Values.Gamma (M := M))
      (v : Fin n → M) (hp : ∀ j, NonzeroRV (v j)) (hq : codeValue ∘ v = γ) :
      ((C.cells i).syntax hc).domain.Realize (Sum.elim (predicateParameterValues B (rvUnitValues x.val)) v) ↔
        (x.val,γ) ∈ ((C.cells i).family X).carrier := by
    have hh := quotientFormulaDomain_full_preimage G.proper G.equal ((C.cells i).syntax hc).domain
      (predicateParameterValues B (rvUnitValues x.val)) NonzeroRV codeValue G.proper_realize G.equal_realize
      (((C.cells i).syntax hc).domainValidity _ _ _ _ (hcells x i)) v
    exact hh.trans ((and_iff_right hp).trans ((Iff.of_eq (congrArg
      (fun q => q ∈ ((C.cells i).syntax hc).gammaDomain (predicateParameterValues B (rvUnitValues x.val))) hq)).trans
        ((C.cells i).family_row X (fun x => hcells x i) x γ).symm))
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨x,γ⟩ hi hj
    have hx := originalGammaFamilyRealization_projection X (C.cells i).domainFormula x γ hi
    obtain ⟨v,hp,hq⟩ := gamma_tuple_code_surjective γ
    exact (hparts ⟨x,hx⟩).2 i j hij v
      ⟨(hmem ⟨x,hx⟩ i γ v hp hq).mpr hi,(hmem ⟨x,hx⟩ j γ v hp hq).mpr hj⟩
  · intro x γ
    constructor
    · intro ht
      have hx := hproj x γ ht
      obtain ⟨v,hp,hq⟩ := gamma_tuple_code_surjective γ
      have hs := (rvGammaFamilySchema_represents T x v).mpr ⟨hp,hq.symm ▸ ht⟩
      obtain ⟨i,hi⟩ := ((hparts ⟨x,hx⟩).1 v).mp hs
      exact ⟨i,(hmem ⟨x,hx⟩ i γ v hp hq).mp hi⟩
    · rintro ⟨i,hi⟩
      have hx := originalGammaFamilyRealization_projection X (C.cells i).domainFormula x γ hi
      obtain ⟨v,hp,hq⟩ := gamma_tuple_code_surjective γ
      have hs := ((hparts ⟨x,hx⟩).1 v).mpr ⟨i,(hmem ⟨x,hx⟩ i γ v hp hq).mpr hi⟩
      have ht := (rvGammaFamilySchema_represents T x v).mp hs |>.2
      exact hq ▸ ht

end DiamondIntegral.Section5
