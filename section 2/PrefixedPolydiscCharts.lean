import «section 2».PrefixedSingletonAtomicity
import «section 2».PolydiscAtomicity

/-! Arbitrary placement of singleton closed coordinates in 2.25 over an
existing ground DC tuple. Every actual chart is tested in the type conclusion. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def DefinableOverDiscGroundAndPolydiscNames (B : ParameterBase M) {k d m : ℕ}
    (ground : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin d → DC (M := M)) (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  ∃ C : PolydiscNaming D,
    DefinableOverFiniteDiscNames (tupleBase B (vfValues C.points))
      (Fin.append ground C.closed) (Fin.append a C.centres) (Fin.append δ C.radii) sn A

def IsAtomicOverDiscGroundAndPolydiscNames (B : ParameterBase M) {k d m : ℕ}
    (ground : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin d → DC (M := M)) (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  DefinableOverDiscGroundAndPolydiscNames B ground a δ D sn A ∧ A.Nonempty ∧
    A ⊆ GammaParameters.sortedUniverse sn ∧
    ∀ C, DefinableOverDiscGroundAndPolydiscNames B ground a δ D sn C → A ⊆ C ∨ Disjoint A C

private theorem chart_product_image {d : ℕ} {D : Fin d → DC (M := M)} (C : PolydiscNaming D) :
    (fun z => z ∘ C.coordinates.symm) '' prefixedNamedPolydisc C.points C.closed C.centres C.radii =
      discNameProduct D := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    apply (C.product_iff _).mpr
    have he : (z ∘ C.coordinates.symm) ∘ C.coordinates = z := by
      funext i
      simp only [Function.comp_apply,C.coordinates.symm_apply_apply]
    rwa [he]
  · intro hx
    refine ⟨x ∘ C.coordinates,(C.product_iff x).mp hx,?_⟩
    funext i
    simp only [Function.comp_apply,C.coordinates.apply_symm_apply]

theorem atomic_in_every_chart_with_disc_ground (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → DC (M := M)) (C : PolydiscNaming D)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverFiniteDiscNames (tupleBase B (vfValues C.points))
      (Fin.append ground C.closed) (Fin.append d C.centres) (Fin.append τ C.radii)
      (fun _ => .vf) (discNameProduct D) := by
  let A' := (fun x : Fin n → M => x ∘ C.coordinates) '' A
  have hA' := hA.image_real C.coordinates
  have hsub' : prefixedNamedPolydisc C.points C.closed C.centres C.radii ⊆ A' := by
    intro z hz
    let x := z ∘ C.coordinates.symm
    have hzx : x ∘ C.coordinates = z := by
      funext i
      simp only [x,Function.comp_apply,C.coordinates.symm_apply_apply]
    have hx : x ∈ discNameProduct D := (C.product_iff x).mpr (hzx.symm ▸ hz)
    exact ⟨x,hsub hx,hzx⟩
  have h := lemma_2_25_singleton_with_disc_ground hc h00 B hΓ unary gamma ground d τ
    C.points C.closed C.centres C.radii A' hA' hsub'
  have hp := h.image_equiv C.coordinates.symm
  rwa [chart_product_image C] at hp

theorem lemma_2_25_disc_ground (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (D : Fin n → DC (M := M)) (hD : Nonempty (PolydiscNaming D))
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ D (fun _ => .vf) (discNameProduct D) := by
  obtain ⟨C⟩ := hD
  have h := atomic_in_every_chart_with_disc_ground hc h00 B hΓ unary gamma ground d τ D C A hA hsub
  refine ⟨⟨C,h.1⟩,h.2.1,h.2.2.1,?_⟩
  rintro T ⟨C',hT⟩
  exact (atomic_in_every_chart_with_disc_ground hc h00 B hΓ unary gamma ground d τ D C' A hA hsub).2.2.2 T hT

theorem lemma_2_25_disc_ground_closed (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (a : Fin n → VF M) (γ : Fin n → GammaInfinity M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct (fun i => closedDiscCode (a i) (γ i)) ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ (fun i => closedDiscCode (a i) (γ i))
      (fun _ => .vf) (discNameProduct (fun i => closedDiscCode (a i) (γ i))) :=
  lemma_2_25_disc_ground hc h00 B hΓ unary gamma ground d τ _ (closedPolydiscNaming_nonempty a γ) A hA hsub

theorem lemma_2_25_disc_ground_open (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : discNameProduct (finitePolydiscNames (fun _ => false) a δ) ⊆ A) :
    IsAtomicOverDiscGroundAndPolydiscNames B ground d τ (finitePolydiscNames (fun _ => false) a δ)
      (fun _ => .vf) (discNameProduct (finitePolydiscNames (fun _ => false) a δ)) :=
  lemma_2_25_disc_ground hc h00 B hΓ unary gamma ground d τ _
    ⟨finitePolydiscNaming (fun _ => false) a δ⟩ A hA hsub

end DiamondIntegral.Section2
