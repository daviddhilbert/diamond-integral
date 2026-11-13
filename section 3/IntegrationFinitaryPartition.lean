import «section 3».IntegrationDiscRVImages
import «section 3».IntegrationPolydiscAtomicity
import «section 2».FinitaryPolydiscPartition
import «section 2».NamedFinitaryPartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Real- and finite-disc-ground Corollary 2.30, supplying every former
unary geometric premise from the checked [18] dependency. -/
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integration_corollary_2_30
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Section2.ParameterBase M))
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : DefinableOver S (fun _ : Fin (n+1) => .vf) {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hfinite : ∀ x ∈ A, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ A, Set.InjOn iRv {y | (x,y) ∈ F}) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ DefinableOver S (fun _ => .vf) V ∧
        ∀ (a : Fin n → Section2.VF M) (δ : Fin n → Section2.Gamma M),
          Section2.namedPolydisc (fun _ => false) a δ ⊆ V →
          Section2.TaggedPolydiscBranchDecomposition (⟨S,∅⟩ : Section2.ParameterBase M) a δ F) ∧
      ∀ x ∈ A, ∃ V ∈ Q, x ∈ V :=
  Section2.corollary_2_30 hc h00 hs S hsmall hΓ (integrationUnaryDiscAtomicityInput hκ hs)
    integrationUnaryOpenDiscRVBaseChangeInput integrationOpenDiscNamesImageInput A hA F hF hfinite hrv

theorem integration_corollary_2_30_disc_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Section2.ParameterBase M))
    {k n : ℕ} (ground : Fin k → Bool) (b : Fin k → Section2.VF M) (τ : Fin k → Section2.Gamma M)
    (A : Set (Fin n → M))
    (hA : Section2.DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : Section2.DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hfinite : ∀ x ∈ A, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ A, Set.InjOn iRv {y | (x,y) ∈ F}) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧
        Section2.DefinableOverFiniteDiscNames ⟨S,∅⟩ ground b τ (fun _ => .vf) V ∧
        ∀ (a : Fin n → Section2.VF M) (δ : Fin n → Section2.Gamma M),
          Section2.namedPolydisc (fun _ => false) a δ ⊆ V →
          Section2.TaggedPolydiscBranchDecompositionOverDiscNames
            (⟨S,∅⟩ : Section2.ParameterBase M) ground b τ a δ F) ∧
      ∀ x ∈ A, ∃ V ∈ Q, x ∈ V :=
  Section2.corollary_2_30_disc_names hc h00 hs hκ S hsmall hΓ
    (integrationUnaryDiscAtomicityInput hκ hs) integrationAtomicDiscGammaBaseChangeInput
    integrationUnaryOpenDiscRVBaseChangeInput integrationOpenDiscNamesImageInput ground b τ A hA F hF hfinite hrv
end DiamondIntegral.Section3
