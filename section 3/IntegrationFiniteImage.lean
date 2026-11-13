import IntegrationSection2.GammaFiniteImage
import «section 2».Conventions

/-! Source [18], Corollary 2.15, using the checked upstream proof and
actual RV values. The original real/Gamma base and its small real part are
retained; the graph contains every code of each Gamma input. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integrationGammaToRVInfinity_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (A : Set (Values.Gamma (M := M))) (f : A → Section2.RVInfinity M)
    (hgraph : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | (z 0,z 1) ∈ IntegrationInACVF.Section2.gammaRVGraph A (fun γ => (f γ).val)}) :
    (Set.range f).Finite := by
  have hf := IntegrationInACVF.Section2.corollary_2_15 hκ hs h00 B hsmall A
    (fun γ => (f γ).val) (fun γ => (f γ).property) hgraph
  have hinj : Function.Injective (fun t : Section2.RVInfinity M => t.val) := Subtype.val_injective
  apply (hf.preimage hinj.injOn).subset
  rintro y ⟨a,rfl⟩
  exact ⟨a,rfl⟩

theorem integrationGammaToRV_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (A : Set (Values.Gamma (M := M))) (f : A → Section2.RV M)
    (hgraph : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | (z 0,z 1) ∈ IntegrationInACVF.Section2.gammaRVGraph A (fun γ => (f γ).val.val)}) :
    (Set.range f).Finite := by
  have hf := integrationGammaToRVInfinity_finite hκ hs h00 B hsmall A (fun γ => (f γ).val) hgraph
  have hinj : Function.Injective (fun t : Section2.RV M => t.val) := Subtype.val_injective
  apply (hf.preimage hinj.injOn).subset
  rintro y ⟨a,rfl⟩
  exact ⟨a,rfl⟩

end DiamondIntegral.Section3
