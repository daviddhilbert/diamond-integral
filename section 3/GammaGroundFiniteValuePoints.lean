import «section 3».RVGammaValueFunctions
import «section 3».GammaGroundRVUnitDomains
import Section3.GammaFiniteOrder
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

theorem gammaGroundGammaPower_definable_iff (T : Set (Fin n → Values.Gamma (M := M))) :
    GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) T ↔
      FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ T) := by
  constructor
  · intro hT
    have hh := FullRawDefinable.reindex
      ((gammaGroundDefinable_iff_full_rv_codes _ (gammaPower_code_proper hc) _).mp hT)
      (Prod.fst : Fin n × Fin 1 → Fin n)
    apply FullBaseAtomicity.OverBase.congr hh
    intro c
    change (∃ hz : (fun ij : Fin n × Fin 1 => c ij.1) ∈ ((volumeGammaSpace hc).power (Fin n)).domain,
      ((volumeGammaSpace hc).power (Fin n)).decode ⟨fun ij => c ij.1,hz⟩ ∈ T) ↔
      (GammaSyntax.Proper c ∧ GammaSyntax.decode c ∈ T)
    have he (hz : (fun ij : Fin n × Fin 1 => c ij.1) ∈ ((volumeGammaSpace hc).power (Fin n)).domain) :
        ((volumeGammaSpace hc).power (Fin n)).decode ⟨fun ij => c ij.1,hz⟩ = GammaSyntax.decode c := by
      funext i
      exact (codeValue_raw ⟨⟨c i,(hz i).1⟩,(hz i).2⟩).symm
    exact ⟨fun ⟨hz,ht⟩ => ⟨hz,(he hz) ▸ ht⟩,fun ⟨hz,ht⟩ => ⟨hz,(he hz).symm ▸ ht⟩⟩
  · exact gammaGroundGammaPower_predicate_definable _

/-- Every coordinate of a point in a finite definable Gamma-tuple set is
individually Gamma-definable over the original mixed ground. -/
theorem fullGamma_finite_tuple_point_definable (T : Set (Fin n → Values.Gamma (M := M)))
    (hT : FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ T)) (hfin : T.Finite)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : δ ∈ T) :
    ∀ i, GammaDefinableClosureAtBase B (δ i) := by
  intro i
  let U := (fun γ : Fin n → Values.Gamma (M := M) => γ i) '' T
  have hp := (hT.reindex (Sum.inr : Fin n → Fin 1 ⊕ Fin n)).and
    (FullGammaSyntax.eq_definable (integrationGammaBase B) (Sum.inr i : Fin 1 ⊕ Fin n) (Sum.inl 0))
  have hU : FullGammaSyntax.Scalar (integrationGammaBase B) U := by
    apply (FullGammaSyntax.scalar_definable_iff U).mp
    apply hp.exists_block.congr
    intro γ
    exact Iff.rfl
  apply (gamma_algebraic_iff_definable_base B (δ i)).mp
  exact ⟨U,(gammaScalar_definable_iff_native B U).mpr hU,hfin.image _,⟨δ,hδ,rfl⟩⟩

theorem gammaGroundGamma_finite_tuple_point_definable
    (T : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))) (hfin : T.carrier.Finite)
    (δ : Fin n → Values.Gamma (M := M)) (hδ : δ ∈ T.carrier) :
    ∀ i, GammaDefinableClosureAtBase B (δ i) :=
  fullGamma_finite_tuple_point_definable T.carrier ((gammaGroundGammaPower_definable_iff _).mp T.definable) hfin δ hδ
end DiamondIntegral.Section3
