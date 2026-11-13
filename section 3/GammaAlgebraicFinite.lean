import Section3.GammaFullDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Saturation gives finiteness for a Gamma-definable set contained in
Gamma acl of a small original real/Gamma base. Entire representative fibres
are covered, without treating any selected representative as algebraic. -/
theorem gamma_finite_of_definable_subset_algebraic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : GammaParameters.Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (Y : Set (Values.Gamma (M := M))) (hY : GammaDefinableOverBase B Y)
    (halg : ∀ γ ∈ Y, GammaAlgebraicAtBase B γ) : Y.Finite := by
  let S := commonRealNames B
  let C : Set (Set M) := {c | ∃ W : Set (Values.Gamma (M := M)), W.Finite ∧
    GammaDefinableOverBase B W ∧ c = Values.gammaPullback W}
  have hrawY := (definableAt_iff_normalized_raw S .rv _).mp hY.common_names |>.1
  have hC (c : Set M) (hc : c ∈ C) :
      @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) c := by
    obtain ⟨W,hW,hWd,rfl⟩ := hc
    exact (definableAt_iff_normalized_raw S .rv _).mp hWd.common_names |>.1
  have hcover : ∀ a ∈ Values.gammaPullback Y, ∃ c ∈ C, a ∈ c := by
    rintro a ⟨ha,h0,haY⟩
    let γ := Values.gammaOf ⟨a,ha⟩ h0
    obtain ⟨W,hWd,hWf,hγW⟩ := halg γ haY
    exact ⟨Values.gammaPullback W,⟨W,hWf,hWd,rfl⟩,ha,h0,hγW⟩
  let A := Values.gammaPullback Y
  have hsN := hs.normalize
  have hsmall := commonRealNames_small hκ B hr hγ
  have hpick : ∃ C₀ : Set (Set M), C₀.Finite ∧ C₀ ⊆ C ∧
      ∀ a ∈ A, ∃ c ∈ C₀, a ∈ c := by
    letI := CanonicalStructure.normalize (M := M)
    exact hsN.definable_finite_subcover S hsmall A hrawY C hC hcover
  obtain ⟨C₀,hC₀,hsub,hcov⟩ := hpick
  choose W hWf hWd hWeq using fun c : C₀ => hsub c.property
  letI := hC₀.fintype
  apply (Set.finite_iUnion hWf).subset
  intro γ hγY
  have hcode : raw (representative γ) ∈ Values.gammaPullback Y :=
    (mem_gammaPullback_code Y (representative γ)).mpr ((representative_value γ).symm ▸ hγY)
  obtain ⟨c,hc,hγc⟩ := hcov _ hcode
  let ci : C₀ := ⟨c,hc⟩
  have hh : raw (representative γ) ∈ Values.gammaPullback (W ci) := (hWeq ci) ▸ hγc
  have hγW := (mem_gammaPullback_code (W ci) (representative γ)).mp hh
  rw [representative_value] at hγW
  exact Set.mem_iUnion.mpr ⟨ci,hγW⟩
end DiamondIntegral.Section3
