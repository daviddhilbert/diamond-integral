import «section 4».GammaOrderLogic
import Section3.GammaClosureLaws
import Section4.GammaPredicates

/-! Explicit auxiliary Gamma parameters, with unchanged real base, and
the bridge from the checked real-code GammaSyntax interface. These lemmas
do not assert descent of a newly defined object to the smaller base. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBaseExtension
open GammaOrderLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def withGamma (B : Base (M := M)) (C : Set (Values.Gamma (M := M))) : Base (M := M) :=
  ⟨B.real, B.gamma ∪ C⟩

theorem definableOverBase_extend (B : Base (M := M)) (C : Set (Values.Gamma (M := M)))
    {n : ℕ} {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A) :
    DefinableOverBase (withGamma B C) sn A := by
  obtain ⟨k, γ, hγ, hR⟩ := hA
  exact ⟨k, γ, (fun i => Or.inl (hγ i)), hR⟩

theorem gammaRelation_extend (B : Base (M := M)) (C : Set (Values.Gamma (M := M)))
    {n : ℕ} {P : Set (Fin n → Values.Gamma (M := M))} (hP : GammaDefinable B P) :
    GammaDefinable (withGamma B C) P := definableOverBase_extend B C hP

theorem gammaSet_extend (B : Base (M := M)) (C : Set (Values.Gamma (M := M)))
    {A : Set (Values.Gamma (M := M))} (hA : GammaDefinableOverBase B A) :
    GammaDefinableOverBase (withGamma B C) A := definableOverBase_extend B C hA

theorem gammaName_extend (B : Base (M := M)) (C : Set (Values.Gamma (M := M)))
    (c : Values.Gamma (M := M)) (hc : c ∈ C) : GammaDefinableClosureAtBase (withGamma B C) c :=
  gamma_name_definable (withGamma B C) c (Or.inr hc)

theorem of_real_syntax (B : Base (M := M)) {n : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M)))
    (hP : SpecialTransformations.Section4.GammaSyntax.Definable B.real (fun z => z ∈ P)) :
    GammaDefinable B P := by
  unfold GammaDefinable
  apply real_definableOverBase
  apply (definableOver_iff_normalized_raw _ _ _).mpr
  exact ⟨hP, fun z hz i => (hz.1 i).1⟩

theorem of_real_set (B : Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : Values.GammaDefinable B.real A) : GammaDefinableOverBase B A :=
  real_definableAtBase B .rv (Values.gammaPullback A) hA

theorem to_common_real_syntax (B : Base (M := M)) {n : ℕ}
    (P : Set (Fin n → Values.Gamma (M := M))) (hP : GammaDefinable B P) :
    SpecialTransformations.Section4.GammaSyntax.Definable (commonRealNames B) (fun z => z ∈ P) := by
  have h : SpecialTransformations.Section3.DefinableOver (commonRealNames B)
      (fun _ : Fin n => .rv) {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ P} :=
    DefinableOverBase.common_names hP
  exact ((definableOver_iff_normalized_raw _ _ _).mp h).1

end DiamondIntegral.Section4.GammaBaseExtension
