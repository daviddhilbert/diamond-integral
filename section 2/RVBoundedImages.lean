import «section 2».RVBoundCoordinates

/-! The RV-valued conclusion of 2.41 follows by taking the actual value
of the output RV element. Both complete graphs keep all source RV tags. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rvScalarFunctionGraph (U : Set (Fin n → RVInfinity M)) (f : (Fin n → RVInfinity M) → RV M) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ u ∈ U, rvInputValues u = z ∘ Sum.inl ∧ (f u).val.val = z (.inr 0)}

theorem rvGammaFunctionGraph_of_rv_definable (S : Set M) (U : Set (Fin n → RVInfinity M))
    (f : (Fin n → RVInfinity M) → RV M) (hf : S.Definable LRV (rvScalarFunctionGraph U f)) :
    S.Definable LRV (rvGammaFunctionGraph U (fun u => GammaParameters.codeValue (f u).val.val)) := by
  have h := rawFibreRelationalImage_definable S _ hf GammaParameters.SameScalar
    (GammaParameters.same_scalar_definable S)
  convert h using 1
  ext z
  constructor
  · rintro ⟨u,hu,huz,hNZ,hout⟩
    have hfuNZ : GammaParameters.NonzeroRV (f u).val.val :=
      ⟨(f u).val.property,fun he => (f u).property (Subtype.ext he)⟩
    exact ⟨(f u).val.val,⟨u,hu,huz,rfl⟩,
      (sameScalar_iff_codeValue_eq _ _ hfuNZ hNZ).mpr hout.symm⟩
  · rintro ⟨v,⟨u,hu,huz,hfv⟩,hsame⟩
    change (f u).val.val = v at hfv
    have he := (sameScalar_iff_codeValue_eq v (z (.inr 0)) hsame.1 hsame.2.1).mp hsame
    rw [← hfv] at he
    exact ⟨u,hu,huz,hsame.2.1,he.symm⟩

theorem lemma_2_41
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (U : Set (Fin n → RVInfinity M)) (hU : S.Definable LRV (rvInputValues '' U))
    (f : (Fin n → RVInfinity M) → RV M) (hf : S.Definable LRV (rvScalarFunctionGraph U f))
    (hbounded : RVValueDoublyBounded U) :
    ∃ γ : Gamma M, ∀ u ∈ U, (γ⁻¹).val ≤ Values.vrv (f u).val ∧ Values.vrv (f u).val ≤ γ.val := by
  obtain ⟨γ,hγ⟩ := lemma_2_41_gamma hc h00 linear hκ hs S hsmall hΓ U hU
    (fun u => GammaParameters.codeValue (f u).val.val)
    (rvGammaFunctionGraph_of_rv_definable S U f hf) hbounded
  refine ⟨γ,fun u hu => ?_⟩
  have h := hγ u hu
  change (γ⁻¹).val ≤ (GammaParameters.codeValue (f u).val.val).val ∧
    (GammaParameters.codeValue (f u).val.val).val ≤ γ.val at h
  rwa [nonzero_rv_codeValue_val (f u).val (f u).property] at h

end DiamondIntegral.Section2
