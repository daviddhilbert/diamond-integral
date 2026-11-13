import «section 3».GammaGroundSortedSyntax
import «section 3».GammaGroundRawDescent
import «section 3».IntegrationGammaParameters
import «section 3».FullRawLogic
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- Equivalence of the two complete-code ground presentations on any
finite real tuple of RV-sort coordinates. -/
theorem gammaGroundRawDefinable_iff_fullRV {ι : Type} [Finite ι]
    (P : (ι → M) → Prop) (hP : ∀ z, P z → ∀ i, iRV (z i)) :
    GammaGroundRawDefinable hc B {z | P z} ↔ FullRawDefinable (integrationGammaBase B) P := by
  letI := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hFin : ∀ z : Fin (Fintype.card ι) → M, P (z ∘ e) → ∀ i, sortEval SortTag.rv (z i) := by
    intro z hz i
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,iRV,sortEval] using hP (z ∘ e) hz (e.symm i)
  have he : ∀ z : ι → M, (z ∘ e.symm) ∘ e = z := by
    intro z
    funext i
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  constructor
  · intro h
    have hraw := h.preimage_comp e
    have hn := (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hFin).mp hraw
    have hh := FullRawDefinable.reindex (integrationGammaDefinable hn) e.symm
    exact FullBaseAtomicity.OverBase.congr hh (fun z => by change P ((z ∘ e.symm) ∘ e) ↔ P z; rw [he z])
  · intro h
    have hh := FullRawDefinable.reindex h e
    have hn := (integrationGammaDefinable_iff hFin).mpr hh
    have hraw := (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hFin).mpr hn
    apply (hraw.preimage_comp e.symm).congr
    intro z
    change P ((z ∘ e.symm) ∘ e) ↔ P z
    rw [he z]

/-- A presented space whose codes are RV-sorted has exactly the same
full-code notion of definability in both original-Gamma-ground APIs. -/
theorem gammaGroundDefinable_iff_full_rv_codes (Q : Space LRV M)
    (hQ : ∀ c ∈ Q.domain, ∀ i, iRV (c i)) (A : Set Q.Carrier) :
    GammaGroundDefinable hc B Q A ↔
      FullRawDefinable (integrationGammaBase B) (fun c => c ∈ Q.preimage A) := by
  rw [gammaGroundDefinable_iff_raw_codes]
  exact gammaGroundRawDefinable_iff_fullRV _ (fun c hc => hQ c hc.choose)
end DiamondIntegral.Section3
