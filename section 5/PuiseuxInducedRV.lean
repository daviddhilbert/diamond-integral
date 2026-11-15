import «section 5».PuiseuxRVLanguage

/-! Remark 5.13 for the actual full induced original-language RV structure.
All original formulas, with parameters from the full Laurent base, are
included in the defining preservation condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section5

abbrev ActualRVUnits := RVCalc.RVUnit (puiseuxValuation ℂ)

def quotientRVAction (ψ : ActualRVUnits ≃* ActualRVUnits) : RV ≃ RV :=
  (rvNormalEquiv.symm.trans (_root_.Equiv.optionCongr ψ.toEquiv)).trans rvNormalEquiv

theorem quotientRVAction_system (η : CompatibleRoots ℂ) (r : RV) :
    quotientRVAction (puiseuxRVAction (puiseuxRootSystemAction η)) r = rvAction η r := by
  have h := rvAction_normal η (rvNormalEquiv.symm r)
  rw [rvNormalEquiv.apply_symm_apply] at h
  exact h.symm

local instance inducedModelStructure : LRV.Structure Carrier := canonicalInterpret

/-- Preserve every relation induced from the full original language, including
formulas with VF quantifiers and arbitrary finite Laurent-base parameters. -/
def PreservesRVFormulas (ψ : ActualRVUnits ≃* ActualRVUnits) : Prop :=
  ∀ (m n : ℕ) (φ : LRV.BoundedFormula (Fin m) n) (v : Fin m → Carrier),
    (∀ a, baseCarrier (v a)) → ∀ r : Fin n → RV,
      φ.Realize v (fun i => Sum.inr (quotientRVAction ψ (r i))) ↔
        φ.Realize v (fun i => Sum.inr (r i))

theorem preservesRVFormulas_of_base (ψ : ActualRVUnits ≃* ActualRVUnits)
    (hψ : ψ ∈ puiseuxRVBaseAutomorphisms ℂ) : PreservesRVFormulas ψ := by
  obtain ⟨η, rfl⟩ := puiseuxRVAutomorphism_lifts ψ hψ
  intro m n φ v hv r
  simpa only [quotientRVAction_system] using original_formula_invariant η φ v hv r

/-- Automorphisms of the full induced RV structure over RV of the Laurent base.
The group language is part of that induced structure. -/
def inducedRVAutSubgroup : Subgroup (ActualRVUnits ≃* ActualRVUnits) :=
  (puiseuxRVBaseAutomorphisms ℂ).copy
    {ψ | ψ ∈ puiseuxRVBaseAutomorphisms ℂ ∧ PreservesRVFormulas ψ} (by
      ext ψ
      constructor
      · exact And.left
      · intro h
        exact ⟨h, preservesRVFormulas_of_base ψ h⟩)

def inducedRVBaseEquiv : inducedRVAutSubgroup ≃* puiseuxRVBaseAutomorphisms ℂ :=
  MulEquiv.subgroupCongr (Subgroup.copy_eq _ _ _)

def puiseuxOriginalRVGaloisEquiv :
    (PuiseuxSeries ℂ ≃ₐ[puiseuxBaseSubfield ℂ] PuiseuxSeries ℂ) ≃* inducedRVAutSubgroup :=
  complexPuiseuxRVGaloisEquiv.trans inducedRVBaseEquiv.symm

def kummerOriginalRVEquiv : CompatibleRoots ℂ ≃* inducedRVAutSubgroup :=
  complexPuiseuxGaloisEquiv.symm.trans puiseuxOriginalRVGaloisEquiv

/-- The two natural identifications in Remark 5.13, on concrete Puiseux
series with their full original-language RV structure and actual Laurent base. -/
def remark_5_13 :
    ((PuiseuxSeries ℂ ≃ₐ[puiseuxBaseSubfield ℂ] PuiseuxSeries ℂ) ≃* CompatibleRoots ℂ) ×
    ((PuiseuxSeries ℂ ≃ₐ[puiseuxBaseSubfield ℂ] PuiseuxSeries ℂ) ≃* inducedRVAutSubgroup) :=
  ⟨complexPuiseuxGaloisEquiv, puiseuxOriginalRVGaloisEquiv⟩

end DiamondIntegral.Section5.PuiseuxOriginal
