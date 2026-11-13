import «section 4».RVResidueCodeRelations

/-! Restricting a residue-field code to an original-base definable RV
subset yields another actual pure-field code over the same ambient space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueRestrictedCodes
open RVResidueChartCodes RVResidueScaledCovers
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cover_restrict {α : Type} {n : ℕ} {D E : Set (α → ModelResidue M)}
    {decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)}
    (C : Cover D decode) (hED : E ⊆ D) : Cover E decode where
  Index := C.Index
  finite := C.finite
  piece := C.piece
  covers x hx := C.covers x (hED hx)
  agrees i x hx hi := C.agrees i x (hED hx) hi

def restrict (hc : CanonicalStructure.IsCanonical (M := M)) {P : Base (M := M)}
    {n : ℕ} {A : Set (Fin n → M)} (C : RawCode A) (E : Set (Fin n → M))
    (hE : DefinableOverBase P (fun _ : Fin n => .rv) E) (hEA : E ⊆ A) : RawCode E where
  chart := {
    arity := C.chart.arity
    domain := {x | x ∈ C.chart.domain ∧ rvValues (C.decode x) ∈ E}
    definable := RVResidueScaledCovers.pullback_definable hc C.chart.definable C.cover E hE }
  decode := C.decode
  bijective := by
    refine ⟨fun _ hx => hx.2, fun _ hx _ hy he => C.bijective.injOn hx.1 hy.1 he, ?_⟩
    intro t ht
    obtain ⟨x, hx, he⟩ := C.bijective.surjOn (hEA ht)
    have hcx : rvValues (C.decode x) = t := he
    have hxe : rvValues (C.decode x) ∈ E := hcx.symm ▸ ht
    exact ⟨x, ⟨hx, hxe⟩, he⟩
  cover := cover_restrict C.cover (fun _ hx => hx.1)

end DiamondIntegral.Section4.RVResidueRestrictedCodes
