import «section 3».GammaRawSelectedMeasuredContractions
import Integration7.StandardContractionOrderTransport

/-! Transporting only the proof of a standard order leaves the actual
measured contractions unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {n a d : ℕ}

theorem gammaStandard_change_order
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a} {σ τ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (h : σ=τ) (hT : GammaProgramDefinable B T.program) :
    GammaProgramDefinable B (standardChangeOrder T h).program := by
  cases h
  exact hT

theorem gammaRaw_measured_change_order
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    {σ τ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (h : σ=τ)
    (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaNativeRawMeasuredContraction C hBC hA hfin (standardChangeOrder T h) (gammaStandard_change_order T h hT) ω =
      gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω := by
  cases h
  rfl

theorem gammaRaw_selected_measured_change_order
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ τ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (h : σ=τ)
    (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin (standardChangeOrder T h) (gammaStandard_change_order T h hT) ω =
      gammaNativeRawSelectedMeasuredContraction C hBC hA ρ hfin T hT ω := by
  cases h
  rfl

end DiamondIntegral.Section3
