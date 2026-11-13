import «section 3».GammaFullRawCommonNames
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem fullGamma_realBase {ι : Type} [Finite ι]
    {P : (ι → Values.Gamma (M := M)) → Prop}
    (hP : FullGammaSyntax.Definable (integrationGammaBase (⟨S,∅⟩ : Base (M := M))) P) :
    GammaSyntax.Definable S P := by
  have hh := gammaFullRaw_common_names (⟨S,∅⟩ : Base (M := M))
    (fun z : ι → M => GammaSyntax.Proper z ∧ P (GammaSyntax.decode z)) hP (fun z hz i => (hz.1 i).1)
  simpa only [GammaSyntax.Definable,commonRealNames,Set.image_empty,Set.union_empty] using hh

/-- A full-code Gamma predicate gives a genuine set in the unchanged
imaginary presentation. All representatives remain in its preimage. -/
theorem gammaPower_predicate_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (P : (Fin n → Values.Gamma (M := M)) → Prop) (hP : GammaSyntax.Definable S P) :
    ((volumeGammaSpace hc).power (Fin n)).Definable S {γ | P γ} := by
  let Q (z : Fin n → M) := GammaSyntax.Proper z ∧ P (GammaSyntax.decode z)
  have hd : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n) {z | Q z} := hP
  rw [canonical_normalize_eq hc] at hd
  have hh : S.Definable LRV {z : Fin n × Fin 1 → M | Q (fun i => z (i,0))} :=
    hd.preimage_comp (fun i : Fin n => (i,(0 : Fin 1)))
  change S.Definable LRV (((volumeGammaSpace hc).power (Fin n)).preimage {γ | P γ})
  have heSet : ((volumeGammaSpace hc).power (Fin n)).preimage {γ | P γ} =
      {z : Fin n × Fin 1 → M | Q (fun i => z (i,0))} := by
    ext z
    change Fin n × Fin 1 → M at z
    change (∃ hz : z ∈ ((volumeGammaSpace hc).power (Fin n)).domain,
      P (((volumeGammaSpace hc).power (Fin n)).decode ⟨z,hz⟩)) ↔
      (GammaSyntax.Proper (fun i => z (i,0)) ∧ P (GammaSyntax.decode (fun i => z (i,0))))
    have he (hz : z ∈ ((volumeGammaSpace hc).power (Fin n)).domain) :
        ((volumeGammaSpace hc).power (Fin n)).decode ⟨z,hz⟩ = GammaSyntax.decode (fun i => z (i,0)) := by
      funext i
      exact (codeValue_raw ⟨⟨z (i,0),(hz i).1⟩,(hz i).2⟩).symm
    exact ⟨fun ⟨hz,hp⟩ => ⟨hz,(he hz) ▸ hp⟩,fun ⟨hz,hp⟩ => ⟨hz,(he hz).symm ▸ hp⟩⟩
  rw [heSet]
  exact hh

def gammaPowerSetOfFull (hc : CanonicalStructure.IsCanonical (M := M))
    (P : (Fin n → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable (integrationGammaBase (⟨S,∅⟩ : Base (M := M))) P) :
    DefSet ((volumeGammaSpace hc).power (Fin n)) S :=
  ⟨{γ | P γ},gammaPower_predicate_definable hc P (fullGamma_realBase hP)⟩
end DiamondIntegral.Section3
