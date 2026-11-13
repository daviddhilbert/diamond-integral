import «section 3».IntegrationDiscAtomicity
import «section 2».PolydiscAtomicity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Lemma 2.25 at the existing closed/open polydisc scopes, with all
[18] geometric inputs supplied by the compiled upstream proofs. -/
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integration_lemma_2_25_closed {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    {d : ℕ} (a : Fin d → Section2.VF M) (γ : Fin d → Section2.GammaInfinity M)
    (A : Set (Fin d → M)) (hA : Section2.GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : Section2.discNameProduct (fun i => Section2.closedDiscCode (a i) (γ i)) ⊆ A) :
    Section2.IsAtomicOverPolydiscNames B (fun i => Section2.closedDiscCode (a i) (γ i)) (fun _ => .vf)
      (Section2.discNameProduct (fun i => Section2.closedDiscCode (a i) (γ i))) :=
  Section2.lemma_2_25_closed h00 B hΓ (integrationUnaryDiscAtomicityInput hκ hs)
    integrationAtomicDiscGammaBaseChangeInput a γ A hA hsub

theorem integration_lemma_2_25_open {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    {d : ℕ} (a : Fin d → Section2.VF M) (δ : Fin d → Section2.Gamma M)
    (A : Set (Fin d → M)) (hA : Section2.GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : Section2.discNameProduct (Section2.finitePolydiscNames (fun _ => false) a δ) ⊆ A) :
    Section2.IsAtomicOverPolydiscNames B (Section2.finitePolydiscNames (fun _ => false) a δ) (fun _ => .vf)
      (Section2.discNameProduct (Section2.finitePolydiscNames (fun _ => false) a δ)) :=
  Section2.lemma_2_25_open h00 B hΓ (integrationUnaryDiscAtomicityInput hκ hs)
    integrationAtomicDiscGammaBaseChangeInput a δ A hA hsub
end DiamondIntegral.Section3
