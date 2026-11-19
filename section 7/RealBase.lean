import «section 7».MeasuredRVBridge
import Section8.GammaRadiusBase

/-! The converse of `MeasuredRVBridge.base_real`: over a canonical model, a
sorted set definable over the real parameters `S` is ground-definable over the
base `⟨S, ∅⟩` with no Gamma names. Together with `base_real` this identifies
Section 4's raw definability over `⟨S, ∅⟩` with Section 6's definability over
`S`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- A sorted set definable over `S` is definable over the base `⟨S, ∅⟩`. -/
theorem real_base (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : S.Definable LRV A)
    (hs : ∀ x ∈ A, ∀ i, sortEval (sn i) (x i)) :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) sn A := by
  refine ⟨0, Fin.elim0, fun i => i.elim0, (with_zero_iff S Fin.elim0 sn A).mpr ?_⟩
  refine (definableOver_iff_normalized_raw S sn A).mpr ⟨?_, hs⟩
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
  exact hA

/-- Raw definability over `⟨S, ∅⟩` is definability over `S` of a sorted set. -/
theorem real_base_iff (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) sn A ↔
      S.Definable LRV A ∧ ∀ x ∈ A, ∀ i, sortEval (sn i) (x i) :=
  ⟨fun h => ⟨MeasuredRVBridge.base_real h, h.proper⟩, fun h => real_base hc h.1 h.2⟩

end DiamondIntegral.Section7.RealBase
