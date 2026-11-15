import «section 3».GammaGroundRVUnitMixedLogic
import «section 5».OriginalEulerRowValues

/-! An actual original-ground RV/Gamma family gives one literal domain
schema with full value representatives and its exact actual Gamma rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def rvGammaFamilySchema
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    GammaDomainFormula B p n (fun _ => .rv) := by
  let R := gammaGroundRVUnitMixedRelation T
  let Q : Set (Fin (p+n) → M) := {z |
    GammaSyntax.Proper (z ∘ Fin.natAdd p) ∧ R (z ∘ Fin.castAdd n) (GammaSyntax.decode (z ∘ Fin.natAdd p))}
  have hraw : FullRawDefinable (integrationGammaBase B) (fun z => z ∈ Q) := by
    have h := FullRawDefinable.reindex (gammaGroundRVUnitMixedRelation_definable hc T)
      (finSumFinEquiv : Fin p ⊕ Fin n → Fin (p+n))
    simpa only [mixedGammaTupleDefinable, Function.comp_def, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Q, R, Set.mem_ofPred_eq] using h
  have hproper : ∀ z ∈ Q, ∀ i, sortEval
      (Fin.append (fun _ : Fin p => .rv) (fun _ : Fin n => .rv) i) (z i) := by
    intro z hz i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left, sortEval, iRV, Function.comp_def] using
        gammaGroundRVUnitMixedRelation_proper T _ _ hz.2 j
    · simpa only [Fin.append_right, sortEval, iRV, Function.comp_def] using (hz.1 j).1
  exact ⟨Q, (integrationGammaDefinable_iff hproper).mpr hraw⟩

theorem rvGammaFamilySchema_row
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) (v : Fin n → M) :
    Fin.append (rvUnitValues x) v ∈ (rvGammaFamilySchema T).val ↔
      Proper v ∧ (x, codeValue ∘ v) ∈ T.carrier := by
  change (GammaSyntax.Proper (Fin.append (rvUnitValues x) v ∘ Fin.natAdd p) ∧
    gammaGroundRVUnitMixedRelation T (Fin.append (rvUnitValues x) v ∘ Fin.castAdd n)
      (GammaSyntax.decode (Fin.append (rvUnitValues x) v ∘ Fin.natAdd p))) ↔ _
  simp only [Function.comp_def, Fin.append_left, Fin.append_right]
  exact and_congr Iff.rfl (gammaGroundRVUnitMixedRelation_unit T x (codeValue ∘ v))


theorem rvGammaFamilySchema_represents
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) :
    gammaFormulaRepresents (gammaDomainSyntax hc B (rvGammaFamilySchema T))
      (predicateParameterValues B (rvUnitValues x)) {γ | (x,γ) ∈ T.carrier} := by
  intro v
  exact (gammaDomainSyntax_realize hc B (rvGammaFamilySchema T) (rvUnitValues x) v).trans
    (rvGammaFamilySchema_row T x v)

theorem rvGammaFamilySchema_valid
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) :
    originalGammaSourceValid hc (rvGammaFamilySchema T) (rvUnitValues x) := by
  let G := nativeGammaRelationSyntax hc
  exact quotientDomainValidity_of_gamma_presentation G.proper G.equal G.proper_realize G.equal_realize
    _ _ _ (rvGammaFamilySchema_represents T x)

theorem rvGammaFamilySchema_quotient_row
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) :
    originalGammaSourceRow hc (rvGammaFamilySchema T) (rvUnitValues x) = {γ | (x,γ) ∈ T.carrier} := by
  ext γ
  constructor
  · rintro ⟨v, hv, hq⟩
    have hm := ((rvGammaFamilySchema_represents T x) v).mp hv
    exact hq ▸ hm.2
  · intro hγ
    obtain ⟨v, hp, hv⟩ := gamma_tuple_code_surjective γ
    exact ⟨v, ((rvGammaFamilySchema_represents T x) v).mpr ⟨hp, hv.symm ▸ hγ⟩, hv⟩

end DiamondIntegral.Section5
