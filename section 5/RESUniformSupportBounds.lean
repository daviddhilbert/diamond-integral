import «section 5».RESValueBoundDefinability
import IntegrationSection6.GammaWitnessUniformity

/-! Genuine saturation gives a uniform finite bound on full value
patterns whenever every row in an original-base definable family is RES. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem res_uniform_support_bound (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {p a : ℕ} (sp : Fin p → SortTag)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (D : GammaDomainFormula B p a sp)
    (hfinite : ∀ z ∈ A, (rawRVValuePattern '' {x : Fin a → M | Fin.append z x ∈ D.val}).Finite) :
    ∃ N : ℕ, ∀ z ∈ A,
      (rawRVValuePattern '' {x : Fin a → M | Fin.append z x ∈ D.val}).ncard ≤ N := by
  let valid (N : ℕ) := {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
    (rawRVValuePattern '' {x : Fin a → M | Fin.append z x ∈ D.val}).Finite ∧
    (rawRVValuePattern '' {x : Fin a → M | Fin.append z x ∈ D.val}).ncard ≤ N}
  have hd (N : ℕ) : DefinableOverBase B sp (valid N) :=
    native_family_value_bound_definable hc B sp N (nativeRVValueSyntax (M := M)) D.val D.property
  obtain ⟨J, hJ⟩ := gamma_finite_witnesses hκ hs hr hγ sp A hA valid hd (by
    intro z hz
    exact ⟨(rawRVValuePattern '' {x : Fin a → M | Fin.append z x ∈ D.val}).ncard,
      hA.proper z hz, hfinite z hz, le_rfl⟩)
  refine ⟨J.sup id, ?_⟩
  intro z hz
  obtain ⟨N, hN, hvalid⟩ := hJ z hz
  exact hvalid.2.2.trans (Finset.le_sup (f := id) hN)

end DiamondIntegral.Section5
