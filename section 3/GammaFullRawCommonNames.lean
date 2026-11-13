import «section 3».FullRawLogic
import «section 3».IntegrationGammaParameters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gammaFullRaw_common_names {α : Type} [Finite α] (B : Base (M := M))
    (P : (α → M) → Prop) (hP : FullRawDefinable (integrationGammaBase B) P)
    (hproper : ∀ a, P a → ∀ i, iRV (a i)) :
    @Set.Definable M (commonRealNames B) LRV (CanonicalStructure.normalize (M := M)) α {a | P a} := by
  letI := Fintype.ofFinite α
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have hFin := FullRawDefinable.reindex hP e
  have hnative : DefinableOverBase B (fun _ => .rv) {z : Fin (Fintype.card α) → M | P (z ∘ e)} := by
    apply (integrationGammaDefinable_iff ?_).mpr hFin
    intro z hz i
    have hh := hproper (z ∘ e) hz (e.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,iRV,sortEval] using hh
  have hd := (definableOver_iff_normalized_raw (commonRealNames B) (fun _ => .rv) _).mp hnative.common_names |>.1
  have hh : @Set.Definable M (commonRealNames B) LRV (CanonicalStructure.normalize (M := M)) α
      {a | P ((a ∘ e.symm) ∘ e)} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.preimage_comp e.symm
  convert hh using 1
  ext a
  have he : (a ∘ e.symm) ∘ e = a := by funext i; simp only [Function.comp_apply,Equiv.symm_apply_apply]
  change P a ↔ P ((a ∘ e.symm) ∘ e)
  rw [he]
end DiamondIntegral.Section3
