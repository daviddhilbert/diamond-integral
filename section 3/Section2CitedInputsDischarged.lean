import «section 2».AtomicDiscGroundChange
import «section 2».AtomicImaginaryGround
import «section 2».BoundaryCoordinates
import «section 2».BoundaryDimension
import «section 2».CitedDiscAtomicity
import «section 2».NamedPolydiscAtomicity
import «section 2».NamedRVConstancy
import «section 2».NamedTaggedImages
import «section 2».PolydiscAtomicity
import «section 2».PolydiscNormalForm
import «section 2».PrefixedPolydiscAtomicity
import «section 2».PrefixedPolydiscCharts
import «section 2».PrefixedSingletonAtomicity
import «section 2».TaggedPolydiscImages
import «section 3».IntegrationDiscAtomicity
import «section 3».IntegrationDiscRVImages
import «section 3».IntegrationPolydiscAtomicity
import «section 3».IntegrationUnaryImages
import «section 3».IntegrationDiscToDisc
import «section 3».IntegrationGammaParameters

/-! Section 2 statements with every cited [18] geometric input supplied by
the compiled upstream proofs (`integration…Input` constructors). Each
`_discharged` statement is the original one with those input arguments
removed. The atomicity constructor needs saturation, which is one of the
paper's standing hypotheses: where the original statement had no saturation
hypothesis (or no bound `ℵ₀ ≤ κ`), it is added in place of the cited input. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section DischargedAll

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_24_disc_names_unary` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_24_disc_names_unary_discharged (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Set M) (hopen : IsOpenDisc D)
    (hD : IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (t : RVInfinity M) :
    IsAtomicOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D}  := by
  apply lemma_2_24_disc_names_unary <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_24_disc_names` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_24_disc_names_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : RVInfinity M) :
    IsAtomicOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j}  := by
  apply lemma_2_24_disc_names <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_24_disc_names_rv_tuple` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_24_disc_names_rv_tuple_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : Fin m → RVInfinity M) :
    IsAtomicOverFiniteDiscNames ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j}  := by
  apply lemma_2_24_disc_names_rv_tuple <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_24_disc_normal_form` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_24_disc_normal_form_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {p k n : ℕ} (points : Fin p → VF M) (closed : Fin k → Bool)
    (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverDiscNamesNormalForm B points closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : RVInfinity M) :
    IsAtomicOverDiscNamesNormalForm (adjoinRV B t) points closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j}  := by
  apply lemma_2_24_disc_normal_form <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

/-- `lemma_2_35_vf` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_35_vf_discharged
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    rvDimension S (tupleRV M '' A ∩ tupleRV M '' Aᶜ) < (n : WithBot ℕ)  := by
  apply lemma_2_35_vf <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_35` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_35_discharged
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A) :
    rvDimension S (rawRVBoundary A) < (n : WithBot ℕ)  := by
  apply lemma_2_35 <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_23_disc_names` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_23_disc_names_discharged (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (hΓ : NontrivialDefinableGamma B)
    {k m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ sn A) (γ : Gamma M) :
    IsAtomicOverFiniteDiscNames (adjoinGamma B γ) closed a δ sn A  := by
  apply lemma_2_23_disc_names <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_23_disc_gamma_tuple` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_23_disc_gamma_tuple_discharged (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    (hΓ : NontrivialDefinableGamma B) {k m l : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ sn A) (γ : Fin l → Gamma M) :
    IsAtomicOverFiniteDiscNames ⟨B.real, B.gamma ∪ Set.range γ⟩ closed a δ sn A  := by
  apply lemma_2_23_disc_gamma_tuple <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_unary` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_unary_discharged (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : ParameterBase M)
    (hΓ : NontrivialDefinableGamma B)
    (A : Set (Fin 1 → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (isClosed : Bool) (c : VF M) (γ : Gamma M)
    (hsub : {x : Fin 1 → M | x 0 ∈ BallImaginaries.underlying
      (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)} ⊆ A) :
    IsAtomicOverFiniteDiscNames B (![isClosed]) (![c]) (![γ]) (fun _ : Fin 1 => .vf)
      {x | x 0 ∈ BallImaginaries.underlying
        (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)}  := by
  apply lemma_2_25_unary <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_finite_names` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_finite_names_discharged (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {n : ℕ} (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) (namedPolydisc closed a δ)  := by
  apply lemma_2_25_finite_names <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_26_disc_names` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_26_disc_names_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (_hfinite : ∀ a ∈ {z | ∀ j, z j ∈ D j}, {y | (a,y) ∈ F}.Finite)
    (_hrv : ∀ a ∈ {z | ∀ j, z j ∈ D j}, Set.InjOn iRv {y | (a,y) ∈ F}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ b ∈ {z | ∀ j, z j ∈ D j},
      iRv '' {y | (a,y) ∈ F} = iRv '' {y | (b,y) ∈ F}  := by
  apply lemma_2_26_disc_names <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_29_disc_names` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_29_disc_names_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (cited : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomicOverFiniteDiscNames B ground d τ (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (hfinite : ∀ a ∈ {a | ∀ j, a j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (hrv : ∀ a ∈ {a | ∀ j, a j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    let A := {a | ∀ j, a j ∈ D j}
    ∃ T : Set (RVInfinity M), T.Finite ∧
      DefinableOverFiniteDiscNames B ground d τ (fun _ : Fin 1 => .rv) {z | z 0 ∈ Subtype.val '' T} ∧
      ∃ g : RVInfinity M → (Fin n → M) → M,
        (∀ t ∈ T,
          DefinableOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin (n+1) => .vf)
            (vfFunctionGraph A (g t)) ∧
          ((∃ c : VF M, ∀ a ∈ A, g t a = c.val) ∨
            (IsAtomicOverFiniteDiscNames (adjoinRV B t) ground d τ (fun _ : Fin 1 => .vf)
                {z | z 0 ∈ g t '' A} ∧ IsOpenDisc (g t '' A))) ∧
          ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g t a = y) ∧
        ∀ a ∈ A, ∀ y, (a, y) ∈ F ↔ ∃ t ∈ T, g t a = y  := by
  apply lemma_2_29_disc_names <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_discharged (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {d : ℕ} (D : Fin d → DC (M := M)) (hD : Nonempty (PolydiscNaming D))
    (A : Set (Fin d → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverPolydiscNames B D (fun _ => .vf) (discNameProduct D)  := by
  apply lemma_2_25 <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_singleton_normal_form` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_singleton_normal_form_discharged (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {p n : ℕ} (points : Fin p → VF M) (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (A : Set (Fin (p+n) → M))
    (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : prefixedNamedPolydisc points closed a δ ⊆ A) :
    IsAtomicOverDiscNamesNormalForm B points closed a δ (fun _ => .vf)
      (prefixedNamedPolydisc points closed a δ)  := by
  apply lemma_2_25_singleton_normal_form <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped Classical
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_with_disc_ground` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_with_disc_ground_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ)
      (fun _ => .vf) (namedPolydisc closed a δ)  := by
  apply lemma_2_25_with_disc_ground <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_disc_ground` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_disc_ground_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → DC (M := M)) (hD : Nonempty (PolydiscNaming D))
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ D (fun _ => .vf) (discNameProduct D)  := by
  apply lemma_2_25_disc_ground <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_disc_ground_closed` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_disc_ground_closed_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (a : Fin n → VF M) (γ : Fin n → GammaInfinity M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct (fun i => closedDiscCode (a i) (γ i)) ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ (fun i => closedDiscCode (a i) (γ i))
      (fun _ => .vf) (discNameProduct (fun i => closedDiscCode (a i) (γ i)))  := by
  apply lemma_2_25_disc_ground_closed <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_disc_ground_open` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_disc_ground_open_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct (finitePolydiscNames (fun _ => false) a δ) ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ (finitePolydiscNames (fun _ => false) a δ)
      (fun _ => .vf) (discNameProduct (finitePolydiscNames (fun _ => false) a δ))  := by
  apply lemma_2_25_disc_ground_open <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_25_singleton_with_disc_ground` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_25_singleton_with_disc_ground_discharged (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k p n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (points : Fin p → VF M) (closed : Fin n → Bool)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (A : Set (Fin (p+n) → M))
    (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : prefixedNamedPolydisc points closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames (tupleBase B (SpecialTransformations.Section4.vfValues points))
      (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) (fun _ => .vf)
      (prefixedNamedPolydisc points closed a δ)  := by
  apply lemma_2_25_singleton_with_disc_ground <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
open DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `lemma_2_29` with its cited [18] inputs supplied by the compiled upstream proofs. -/
theorem lemma_2_29_discharged (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, OpenDiscImageInput E)
    {n : ℕ} (D : Fin n → Set M) (hopen : ∀ j, IsOpenDisc (D j))
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z, z (Fin.last n)) ∈ F})
    (hfinite : ∀ a ∈ {a | ∀ j, a j ∈ D j}, {y | (a, y) ∈ F}.Finite)
    (hrv : ∀ a ∈ {a | ∀ j, a j ∈ D j}, Set.InjOn iRv {y | (a, y) ∈ F}) :
    let A := {a | ∀ j, a j ∈ D j}
    ∃ T : Set (RVInfinity M), T.Finite ∧
      GammaParameters.DefinableAtBase B .rv (Subtype.val '' T) ∧
      ∃ g : RVInfinity M → (Fin n → M) → M,
        (∀ t ∈ T,
          GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ : Fin (n+1) => .vf)
            (vfFunctionGraph A (g t)) ∧
          ((∃ c : VF M, ∀ a ∈ A, g t a = c.val) ∨
            (IsAtomic (adjoinRV B t) (fun _ : Fin 1 => .vf)
                {z | z 0 ∈ g t '' A} ∧ IsOpenDisc (g t '' A))) ∧
          ∀ a ∈ A, ∀ y, ((a, y) ∈ F ∧ iRv y = t.val) ↔ g t a = y) ∧
        ∀ a ∈ A, ∀ y, (a, y) ∈ F ↔ ∃ t ∈ T, g t a = y  := by
  apply lemma_2_29 <;> first | assumption | exact DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput _ | exact DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput hκ hs _ | exact DiamondIntegral.Section3.integrationDiscToDiscPartitionInput hκ hs _ | exact DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput _ | exact DiamondIntegral.Section3.integrationOpenDiscNamesImageInput _ | exact DiamondIntegral.Section3.integrationOpenDiscImageInput _ | exact DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete h00 _ | exact DiamondIntegral.Section3.integrationPrimitiveImageInput _

end DiamondIntegral.Section3
end

end DischargedAll
