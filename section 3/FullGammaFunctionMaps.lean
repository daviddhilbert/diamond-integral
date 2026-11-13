import «section 3».GammaGroundRVUnitDomains
import «section 3».FullGammaFunctions
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

/-- An actual full-code Gamma function supplies an actual map in the
Gamma-ground presentation, with every target representative in its graph. -/
def fullGammaFunctionMap (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    GammaGroundMap (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
      (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) := by
  let Q := ((volumeGammaSpace hc).power (Fin n)).prod (volumeGammaSpace hc)
  refine ⟨fun a => ⟨f a.val,Set.mem_univ _⟩,?_⟩
  have hQ : ∀ z ∈ Q.domain, ∀ i, iRV (z i) := by
    intro z hz i
    cases i with
    | inl i => exact gammaPower_code_proper hc _ hz.1 i
    | inr i =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hz.2.1
  apply (gammaGroundDefinable_iff_full_rv_codes Q hQ _).mpr
  let e : Fin n ⊕ Fin 1 → (Fin n × Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (i,0)) Sum.inr
  have hh := FullRawDefinable.reindex hf e
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change (Fin n × Fin 1) ⊕ Fin 1 → M at z
  change (GammaSyntax.Proper (z ∘ e) ∧
    f (GammaSyntax.decode (z ∘ e) ∘ Sum.inl) = GammaSyntax.decode (z ∘ e) (.inr 0)) ↔
    ∃ hz : z ∈ Q.domain, ∃ a : GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)),
      a.val = ((volumeGammaSpace hc).power (Fin n)).decode ⟨z ∘ Sum.inl,hz.1⟩ ∧
        f a.val = (volumeGammaSpace hc).decode ⟨z ∘ Sum.inr,hz.2⟩
  have hproper : GammaSyntax.Proper (z ∘ e) ↔ z ∈ Q.domain := by
    constructor
    · intro hz
      exact ⟨fun i => hz (.inl i),hz (.inr 0)⟩
    · intro hz i
      cases i with
      | inl i => exact hz.1 i
      | inr i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact hz.2
  have hleft (hz : z ∈ Q.domain) :
      ((volumeGammaSpace hc).power (Fin n)).decode ⟨z ∘ Sum.inl,hz.1⟩ = GammaSyntax.decode (z ∘ e) ∘ Sum.inl := by
    funext i
    exact (codeValue_raw ⟨⟨z (.inl (i,0)),(hz.1 i).1⟩,(hz.1 i).2⟩).symm
  have hright (hz : z ∈ Q.domain) :
      (volumeGammaSpace hc).decode ⟨z ∘ Sum.inr,hz.2⟩ = GammaSyntax.decode (z ∘ e) (.inr 0) :=
    (codeValue_raw ⟨⟨z (.inr 0),hz.2.1⟩,hz.2.2⟩).symm
  constructor
  · rintro ⟨hz,he⟩
    have hdom := hproper.mp hz
    refine ⟨hdom,⟨_,Set.mem_univ _⟩,rfl,?_⟩
    exact (congrArg f (hleft hdom)).trans (he.trans (hright hdom).symm)
  · rintro ⟨hz,a,ha,he⟩
    refine ⟨hproper.mpr hz,?_⟩
    exact (congrArg f (ha.trans (hleft hz))).symm.trans (he.trans (hright hz))
end DiamondIntegral.Section3
