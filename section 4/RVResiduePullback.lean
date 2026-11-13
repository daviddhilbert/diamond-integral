import «section 4».RVMeasuredCharts
import Section4.ResidueNormalization
import Section4.ResidueQFInterpretation
import Section4.RVValueFibres

/-! Pure-field pullbacks of actual RV sets. Auxiliary RV scale factors
are proof parameters; this construction makes no claim that they are
definable over the original base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResiduePullback
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def ofRaw {B : Base (M := M)} {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A) :
    DefSet (rawRVSpace (M := M) n) (commonRealNames B) where
  carrier := {t | rvValues t ∈ A}
  definable := by
    have he : (rawRVSpace (M := M) n).preimage {t | rvValues t ∈ A} = A := by
      ext x
      constructor
      · rintro ⟨hx, ha⟩
        change rvValues ((rawRVSpace n).decode ⟨x, hx⟩) ∈ A at ha
        rwa [rvValues_decode] at ha
      · intro hx
        have hs : x ∈ (rawRVSpace (M := M) n).domain :=
          ⟨fun i => ⟨x i, hA.proper x hx i⟩, rfl⟩
        refine ⟨hs, ?_⟩
        change rvValues ((rawRVSpace n).decode ⟨x, hs⟩) ∈ A
        rwa [rvValues_decode]
    change (commonRealNames B).Definable LRV ((rawRVSpace n).preimage
      {t : Fin n → CanonicalRV.RVSort M | rvValues t ∈ A})
    exact Eq.mpr (congrArg (fun U : Set (Fin n → M) =>
      (commonRealNames B).Definable LRV U) he) hA.common_names.raw_definable

theorem scaled_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (s : Fin n → CanonicalRV.RVSort M) :
    PureDef {x : Fin n → ModelResidue M | rvValues (residueScale s x) ∈ A} :=
  residue_pullback_pure hc (ofRaw A hA) s

theorem scaled_coordinates_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {n : ℕ} {α : Type} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (s : Fin n → CanonicalRV.RVSort M) (coord : Fin n → α) :
    PureDef {x : α → ModelResidue M |
      rvValues (residueScale s (x ∘ coord)) ∈ A} := by
  exact (scaled_definable hc A hA s).preimage_comp coord

theorem zeroPattern_definable {n : ℕ} (s : Fin n → CanonicalRV.RVSort M) :
    PureDef {x : Fin n → ModelResidue M | residueZeroPattern s x} := by
  have h (i : Fin n) : PureDef {x : Fin n → ModelResidue M | s i = 0 → x i = 0} := by
    by_cases hi : s i = 0
    · simpa only [hi, true_implies] using (pure_proj i).eq_const (0 : ModelResidue M)
    · simpa only [hi, false_implies] using (pure_proposition (K := ModelResidue M)
        (ι := Fin n) True)
  change PureDef {x | ∀ i, s i = 0 → x i = 0}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite h

theorem normalized_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) : PureDef (normalizedResidueSet A s) :=
  (residue_pullback_pure hc A s).inter (zeroPattern_definable s)

theorem normalized_fibre_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (γ : Fin n → Values.GammaTop (M := M)) (hγ : ∀ i, RVValueDefinable S (γ i))
    (s : Fin n → CanonicalRV.RVSort M) :
    PureDef (normalizedResidueSet (rvValueFibre A γ hγ) s) :=
  normalized_definable hc (rvValueFibre A γ hγ) s

end DiamondIntegral.Section4.RVResiduePullback
