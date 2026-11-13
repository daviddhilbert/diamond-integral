import «section 3».GammaGroundGammaRVCodeLift
import «section 3».FullGammaPartialFunctions
import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundVolumeForms
import «section 3».GammaGroundRVUnitDomains
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- A partial actual Gamma form has a full original-ground Gamma code
graph, retaining every coordinate and every code representative. -/
theorem gammaGroundGammaForm_full_graph
    (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    FullGammaSyntax.Definable (integrationGammaBase B)
      (fun z : Fin n ⊕ Fin 1 → Values.Gamma (M := M) =>
        ∃ a : G, a.val = z ∘ Sum.inl ∧ (w a).val = z (.inr 0)) := by
  let Q := ((volumeGammaSpace hc).power (Fin n)).prod (volumeGammaSpace hc)
  have hQ : ∀ z ∈ Q.domain, ∀ i, iRV (z i) := by
    intro z hz i
    cases i with
    | inl i => exact gammaPower_code_proper hc _ hz.1 i
    | inr i =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hz.2.1
  have hg := (gammaGroundDefinable_iff_full_rv_codes Q hQ _).mp w.graph_definable
  let e : (Fin n × Fin 1) ⊕ Fin 1 → Fin n ⊕ Fin 1 := Sum.elim (fun i => .inl i.1) Sum.inr
  have hh := FullRawDefinable.reindex hg e
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change (∃ hz : (z ∘ e) ∈ Q.domain, ∃ a : G,
      a.val = ((volumeGammaSpace hc).power (Fin n)).decode ⟨(z ∘ e) ∘ Sum.inl,hz.1⟩ ∧
        (w a).val = (volumeGammaSpace hc).decode ⟨(z ∘ e) ∘ Sum.inr,hz.2⟩) ↔
    (GammaSyntax.Proper z ∧ ∃ a : G, a.val = GammaSyntax.decode z ∘ Sum.inl ∧
      (w a).val = GammaSyntax.decode z (.inr 0))
  have hp : (z ∘ e) ∈ Q.domain ↔ GammaSyntax.Proper z := by
    constructor
    · intro hz i
      cases i with
      | inl i => exact hz.1 i
      | inr i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact hz.2
    · intro hz
      exact ⟨fun i => hz (.inl i),hz (.inr 0)⟩
  have hl (hz : (z ∘ e) ∈ Q.domain) :
      ((volumeGammaSpace hc).power (Fin n)).decode ⟨(z ∘ e) ∘ Sum.inl,hz.1⟩ = GammaSyntax.decode z ∘ Sum.inl := by
    funext i
    exact (codeValue_raw ⟨⟨z (.inl i),(hz.1 i).1⟩,(hz.1 i).2⟩).symm
  have hr (hz : (z ∘ e) ∈ Q.domain) :
      (volumeGammaSpace hc).decode ⟨(z ∘ e) ∘ Sum.inr,hz.2⟩ = GammaSyntax.decode z (.inr 0) :=
    (codeValue_raw ⟨⟨z (.inr 0),hz.2.1⟩,hz.2.2⟩).symm
  constructor
  · rintro ⟨hz,a,ha,hw⟩
    exact ⟨hp.mp hz,a,ha.trans (hl hz),hw.trans (hr hz)⟩
  · rintro ⟨hz,a,ha,hw⟩
    exact ⟨hp.mpr hz,a,ha.trans (hl (hp.mpr hz)).symm,hw.trans (hr (hp.mpr hz)).symm⟩

def gammaGroundGammaFormPartialFunction
    (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    FullGammaPartialFunction (integrationGammaBase B) n where
  graph γ δ := ∃ a : G, a.val = γ ∧ (w a).val = δ
  definable := gammaGroundGammaForm_full_graph G w
  functional := by
    rintro γ δ ε ⟨a,ha,hδ⟩ ⟨b,hb,hε⟩
    have he : a = b := Subtype.ext (ha.trans hb.symm)
    exact hδ.symm.trans ((congrArg (fun x : G => (w x).val) he).trans hε)

/-- Totalization by one outside the Gamma domain keeps the same ground
and agrees with the actual form on every point of its original domain. -/
theorem gammaGroundGammaForm_total_function
    (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    ∃ f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M),
      FullGammaFunction (integrationGammaBase B) f ∧ ∀ a : G, f a.val = (w a).val := by
  let D := gammaGroundGammaFormPartialFunction G w
  exact ⟨D.eval,D.eval_definable,fun a => D.eval_eq a.val (w a).val ⟨a,rfl,rfl⟩⟩
end DiamondIntegral.Section3
