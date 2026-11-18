import «section 2».RVBoundedImages
import «section 2».GammaCurveSelectionFailure
import «section 2».PartitionBoundedMixed
import «section 5».GammaQEFiniteLaws
import «section 3».GammaGroundRVBoundedImages

/-! Lemma 2.41, Remark 2.47 and Lemma 2.53 without the unary Γ
rational-affine input: that input is the theorem
`Section5.GammaQE.gamma_piecewise_rational_affine`, proved from RV quantifier
elimination with no further hypotheses. Statements are otherwise verbatim. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_2_41_gamma` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem lemma_2_41_gamma_discharged
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (U : Set (Fin n → RVInfinity M)) (hU : S.Definable LRV (rvInputValues '' U))
    (f : (Fin n → RVInfinity M) → Gamma M) (hf : S.Definable LRV (rvGammaFunctionGraph U f))
    (hbounded : RVValueDoublyBounded U) :
    ∃ γ : Gamma M, ∀ u ∈ U, γ⁻¹ ≤ f u ∧ f u ≤ γ  := by
  apply lemma_2_41_gamma (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

/-- `lemma_2_41` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem lemma_2_41_discharged
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (U : Set (Fin n → RVInfinity M)) (hU : S.Definable LRV (rvInputValues '' U))
    (f : (Fin n → RVInfinity M) → RV M) (hf : S.Definable LRV (rvScalarFunctionGraph U f))
    (hbounded : RVValueDoublyBounded U) :
    ∃ γ : Gamma M, ∀ u ∈ U, (γ⁻¹).val ≤ Values.vrv (f u).val ∧ Values.vrv (f u).val ≤ γ.val  := by
  apply lemma_2_41 (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

/-- `remark_2_47` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem remark_2_47_discharged (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Gamma M)) (f h : Gamma M → Gamma M)
    (hf : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1))
    (hh : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ h (z 0) = z 1))
    (hpos : ∀ t ∈ D, 1 < h t) :
    ∃ N ε : Gamma M, 1 < ε ∧ ∀ t ∈ D, N < f t → ε ≤ h t  := by
  apply remark_2_47 (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

/-- `remark_2_47_no_approach` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem remark_2_47_no_approach_discharged (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Gamma M)) (f h : Gamma M → Gamma M)
    (hf : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1))
    (hh : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ h (z 0) = z 1))
    (hpos : ∀ t ∈ D, 1 < h t)
    (happroach : ∀ N ε : Gamma M, 1 < ε → ∃ t ∈ D, N < f t ∧ h t < ε) : False  := by
  exact remark_2_47_no_approach h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) S hΓ D f h hf hh hpos happroach

/-- `lemma_2_53` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem lemma_2_53_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n m)) (hA : S.Definable LRV (mixedTuple '' A))
    (hRV : RVValueDoublyBounded (Prod.snd '' A))
    (hclosed : ∀ t ∈ Prod.snd '' A, IsClosed (vfFibre A t))
    (hbounded : ∀ t ∈ Prod.snd '' A, ∃ η : Gamma M,
      ∀ a ∈ vfFibre A t, ∀ i, η.val ≤ vfValue (a i))
    (p : Mixed M n m → Gamma M) (hp : IsMixedOpenDiscPartition A p)
    (hpdef : S.Definable LRV (mixedGammaGraph A p)) :
    ∃ γ : Gamma M, ∀ x ∈ A, γ⁻¹ ≤ p x ∧ p x ≤ γ  := by
  apply lemma_2_53 (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

/-- `lemma_2_53_image_bounds` with the unary Γ rational-affine input discharged by
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem lemma_2_53_image_bounds_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n m)) (hA : S.Definable LRV (mixedTuple '' A))
    (hRV : RVValueDoublyBounded (Prod.snd '' A))
    (hclosed : ∀ t ∈ Prod.snd '' A, IsClosed (vfFibre A t))
    (hbounded : ∀ t ∈ Prod.snd '' A, ∃ η : Gamma M,
      ∀ a ∈ vfFibre A t, ∀ i, η.val ≤ vfValue (a i))
    (p : Mixed M n m → Gamma M) (hp : IsMixedOpenDiscPartition A p)
    (hpdef : S.Definable LRV (mixedGammaGraph A p)) :
    BddBelow (p '' A) ∧ BddAbove (p '' A)  := by
  apply lemma_2_53_image_bounds (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

end DiamondIntegral.Section3
open SpecialTransformations.DefinableGeometry
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- `lemma_2_41_gammaGround` with the unary Γ rational-affine input discharged. -/
theorem lemma_2_41_gammaGround_discharged
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (ground : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk ground.real < κ)
    (hΓ : Section2.NontrivialDefinableGamma (⟨ground.real,∅⟩ : Section2.ParameterBase M))
    (U : Set (Fin n → Section2.RVInfinity M)) (hU : GammaGroundDefinable hc ground (rawRVSpace n) U)
    (f : (Fin n → Section2.RVInfinity M) → Section2.RV M)
    (hf : GammaGroundDefinable hc ground ((rawRVSpace n).prod (rawRVSpace 1))
      {p | rvScalarGraphRelation U f p.1 p.2})
    (hbounded : Section2.RVValueDoublyBounded U) :
    ∃ γ : Section2.Gamma M, ∀ u ∈ U,
      (γ⁻¹).val ≤ Values.vrv (f u).val ∧ Values.vrv (f u).val ≤ γ.val  := by
  apply lemma_2_41_gammaGround (linear := Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) <;> assumption

end DiamondIntegral.Section3
