import «section 2».RVGammaBounds
import «section 2».RVMapGraphs

/-! The actual RV-infinity coordinate interface for 2.41. A double
bound itself excludes every zero/infinity tag; zero input arity remains
included. Full Gamma graphs contain every proper output code. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def RVValueDoublyBounded (U : Set (Fin n → RVInfinity M)) : Prop :=
  ∃ β : Gamma M, ∀ u ∈ U, ∀ i, (β⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ β.val

theorem RVValueDoublyBounded.nonzero {U : Set (Fin n → RVInfinity M)} (hU : RVValueDoublyBounded U) :
    ∀ u ∈ U, ∀ i, u i ≠ rvZero M := by
  obtain ⟨β,hβ⟩ := hU
  intro u hu i he
  have h := (hβ u hu i).2
  rw [he] at h
  change Values.infinity ≤ β.val at h
  exact β.property (le_antisymm (Values.le_infinity _) h)

theorem nonzero_rv_codeValue_val (t : RVInfinity M) (ht : t ≠ rvZero M) :
    (GammaParameters.codeValue t.val).val = Values.vrv t := by
  have hNZ : GammaParameters.NonzeroRV t.val := ⟨t.property,fun he => ht (Subtype.ext he)⟩
  simp only [GammaParameters.codeValue,dite_eq_left hNZ,GammaParameters.value,Values.gammaOf]

def rvGammaFunctionGraph (U : Set (Fin n → RVInfinity M)) (f : (Fin n → RVInfinity M) → Gamma M) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ u ∈ U, rvInputValues u = z ∘ Sum.inl ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    GammaParameters.codeValue (z (.inr 0)) = f u}

noncomputable def rvGammaRawExtension (U : Set (Fin n → RVInfinity M))
    (f : (Fin n → RVInfinity M) → Gamma M) (x : Fin n → M) : Gamma M := by
  classical
  exact if hx : x ∈ rvInputValues '' U then f hx.choose else 1

theorem rvGammaRawExtension_on (U : Set (Fin n → RVInfinity M))
    (f : (Fin n → RVInfinity M) → Gamma M) (u : Fin n → RVInfinity M) (hu : u ∈ U) :
    rvGammaRawExtension U f (rvInputValues u) = f u := by
  classical
  have hx : rvInputValues u ∈ rvInputValues '' U := Set.mem_image_of_mem _ hu
  rw [rvGammaRawExtension,dite_eq_left hx]
  exact congrArg f (rvInputValues_injective hx.choose_spec.2)

theorem rvGammaFunctionGraph_raw_eq (U : Set (Fin n → RVInfinity M))
    (f : (Fin n → RVInfinity M) → Gamma M) :
    rvGammaFunctionGraph U f = rawGammaFamilyGraph (rvInputValues '' U) (fun x => {rvGammaRawExtension U f x}) := by
  ext z
  constructor
  · rintro ⟨u,hu,huz,hNZ,hout⟩
    have hf : rvGammaRawExtension U f (z ∘ Sum.inl) = f u := by
      rw [← huz]
      exact rvGammaRawExtension_on U f u hu
    exact ⟨⟨u,hu,huz⟩,hNZ,hout.trans hf.symm⟩
  · rintro ⟨⟨u,hu,huz⟩,hNZ,hout⟩
    have he : GammaParameters.codeValue (z (.inr 0)) = rvGammaRawExtension U f (z ∘ Sum.inl) := hout
    rw [← huz,rvGammaRawExtension_on U f u hu] at he
    exact ⟨u,hu,huz,hNZ,he⟩

theorem lemma_2_41_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (U : Set (Fin n → RVInfinity M)) (hU : S.Definable LRV (rvInputValues '' U))
    (f : (Fin n → RVInfinity M) → Gamma M) (hf : S.Definable LRV (rvGammaFunctionGraph U f))
    (hbounded : RVValueDoublyBounded U) :
    ∃ γ : Gamma M, ∀ u ∈ U, γ⁻¹ ≤ f u ∧ f u ≤ γ := by
  have hNZ : ∀ x ∈ rvInputValues '' U, ∀ i, GammaParameters.NonzeroRV (x i) := by
    rintro x ⟨u,hu,rfl⟩ i
    exact ⟨(u i).property,fun he => hbounded.nonzero u hu i (Subtype.ext he)⟩
  have hcodeBound : RVCodeDoublyBounded (rvInputValues '' U) := by
    obtain ⟨β,hβ⟩ := hbounded
    refine ⟨β,?_⟩
    rintro x ⟨u,hu,rfl⟩ i
    change (β⁻¹).val ≤ (GammaParameters.codeValue (u i).val).val ∧
      (GammaParameters.codeValue (u i).val).val ≤ β.val
    rw [nonzero_rv_codeValue_val (u i) (RVValueDoublyBounded.nonzero ⟨β,hβ⟩ u hu i)]
    exact hβ u hu i
  rw [rvGammaFunctionGraph_raw_eq] at hf
  obtain ⟨γ,hγ⟩ := lemma_2_41_gamma_raw hc h00 linear hκ hs S hsmall hΓ _ hU hNZ
    (rvGammaRawExtension U f) hf hcodeBound
  refine ⟨γ,fun u hu => ?_⟩
  simpa only [rvGammaRawExtension_on U f u hu] using hγ (rvInputValues u) (Set.mem_image_of_mem _ hu)

end DiamondIntegral.Section2
