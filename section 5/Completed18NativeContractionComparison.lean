import IntegrationSection5.FiniteNormalization
import IntegrationSection6.FiniteGammaAmbientIsos
import IntegrationSection6.FiniteStandardContractions

/-! The completed Section 5 actual RV-category isomorphism gives exactly
the normalized finite RV isomorphism consumed by Section 6. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def native_contraction_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) {B : Base (M := M)} (hr : Cardinal.mk B.real < κ)
    {S : Set M} (hBS : B.real ⊆ S) {n m : ℕ} {U : DefSet (M := M) S n m}
    (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M),{r : Fin m → RV (M := M) | (x,r)∈carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (D : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hD : GammaProgramDefinable B D.program)
    (e : IntegrationInACVF.Section5.GammaRVIso B C.contractionObject D.contractionObject) :
    SpecialTransformations.Section7.GammaRVIso
      (IntegrationInACVF.Section6.FiniteRV.gammaFiniteContraction hκ hs hr hBS hU hfin C hC).toGammaRVObject
      (IntegrationInACVF.Section6.FiniteRV.gammaFiniteContraction hκ hs hr hBS hU hfin D hD).toGammaRVObject := by
  let P := IntegrationInACVF.Section6.FiniteRV.gammaFiniteContraction hκ hs hr hBS hU hfin C hC
  let Q := IntegrationInACVF.Section6.FiniteRV.gammaFiniteContraction hκ hs hr hBS hU hfin D hD
  let PA : IntegrationInACVF.Section6.FiniteRV.GammaObjectAt B S n :=
    ⟨⟨C.normalizedObject,P.finite_volume⟩,hBS,P.domain_graph,P.volume_graph⟩
  let QA : IntegrationInACVF.Section6.FiniteRV.GammaObjectAt B S n :=
    ⟨⟨D.normalizedObject,Q.finite_volume⟩,hBS,Q.domain_graph,Q.volume_graph⟩
  let eC := gamma_firstVolumeIso (Map.image (rawLabelMap C.target)) C.volumeIndex
    (C.gamma_rv_domain (gamma_program_final_set C.program hC))
  let eD := gamma_firstVolumeIso (Map.image (rawLabelMap D.target)) D.volumeIndex
    (D.gamma_rv_domain (gamma_program_final_set D.program hD))
  let eN := eC.symm.trans (e.trans eD)
  let f : IntegrationInACVF.Section6.FiniteRV.GammaIsoAt PA QA :=
    IntegrationInACVF.Section6.FiniteRV.GammaIsoAt.ofAmbient eN.iso eN.hom_graph
  exact f.toGamma

end DiamondIntegral.Section5
