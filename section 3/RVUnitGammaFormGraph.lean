import «section 3».RVGammaValueFunctions
import «section 3».GammaGroundRVUnitDomains
import «section 3».GammaGroundMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaVolume_code_decode (c : (volumeGammaSpace hc).domain) :
    (volumeGammaSpace hc).decode c = codeValue (c.val (0 : Fin 1)) :=
  (codeValue_raw ⟨⟨c.val (0 : Fin 1),c.property.1⟩,c.property.2⟩).symm

/-- An actual Gamma-ground volume map has exactly the full mixed-code
graph required by the local Gamma-value function theorem. -/
theorem gammaGroundRVUnitGammaForm_graph
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (w : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    mixedGammaTupleDefinable B (rvUnitGammaGraph A.carrier (fun a => (w a).val)) := by
  let Q := (rawRVUnitSpace (M := M) n).prod (volumeGammaSpace hc)
  have hQ : ∀ z ∈ Q.domain, ∀ i, iRV (z i) := by
    intro z hz i
    cases i with
    | inl i => exact rawRVUnitSpace_code_proper _ hz.1 i
    | inr i =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hz.2.1
  have hr := (gammaGroundDefinable_iff_full_rv_codes Q hQ _).mp w.graph_definable
  apply FullBaseAtomicity.OverBase.congr hr
  intro z
  change Fin n ⊕ Fin 1 → M at z
  change (∃ hz : z ∈ Q.domain,
    ∃ a : A, a.val = (rawRVUnitSpace n).decode ⟨z ∘ Sum.inl,hz.1⟩ ∧
      (w a).val = (volumeGammaSpace hc).decode ⟨z ∘ Sum.inr,hz.2⟩) ↔
    (GammaSyntax.Proper (z ∘ Sum.inr) ∧
      ∃ a : A, rvUnitValues a.val = z ∘ Sum.inl ∧ (w a).val = GammaSyntax.decode (z ∘ Sum.inr) 0)
  constructor
  · rintro ⟨hz,a,ha,hw⟩
    refine ⟨?_,a,(congrArg rvUnitValues ha).trans (rvUnitValues_decode _),?_⟩
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hz.2
    · exact hw.trans (gammaVolume_code_decode (hc := hc) ⟨z ∘ Sum.inr,hz.2⟩)
  · rintro ⟨hγ,a,ha,hw⟩
    have hu : z ∘ Sum.inl ∈ (rawRVUnitSpace (M := M) n).domain := ⟨a.val,ha⟩
    have hg : z ∘ Sum.inr ∈ (volumeGammaSpace hc).domain := hγ 0
    refine ⟨⟨hu,hg⟩,a,rvUnitValues_injective (ha.trans (rvUnitValues_decode (M := M) (n := n) ⟨z ∘ Sum.inl,hu⟩).symm),?_⟩
    exact hw.trans (gammaVolume_code_decode (hc := hc) ⟨z ∘ Sum.inr,hg⟩).symm
end DiamondIntegral.Section3
