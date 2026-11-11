import «section 2».PolydiscCharts

/-!
# Lemma 2.25 over the actual polydisc-name tuple

Finite reindexing removes the singleton-first convention. Definability
uses a chart of the given DC tuple: only its uniquely decoded singleton
points enter the real base. The theorem works for every such chart, so
the complete-type assertion tests all the chart presentations.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A permutation of the real output coordinates retains every named disc. -/
theorem IsAtomicOverFiniteDiscNames.image_equiv {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {A : Set (Fin n → M)}
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) A)
    (e : Fin m ≃ Fin n) :
    IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) ((fun x => x ∘ e) '' A) := by
  refine ⟨hA.1.image_real e, hA.2.1.image _, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩ i
    exact hA.2.2.1 hy (e i)
  · intro C hC
    have hpre := hC.preimage_real (fun _ : Fin n => .vf) e
    rcases hA.2.2.2 _ hpre with hsub | hdis
    · left
      rintro x ⟨y, hy, rfl⟩
      exact (hsub hy).1
    · right
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy, rfl⟩ hx
      exact Set.disjoint_left.mp hdis hy ⟨hx, hA.2.2.1 hy⟩

def DefinableOverPolydiscNames (B : ParameterBase M) {d m : ℕ}
    (D : Fin d → DC (M := M)) (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  ∃ C : PolydiscNaming D,
    DefinableOverFiniteDiscNames (tupleBase B (SpecialTransformations.Section4.vfValues C.points))
      C.closed C.centres C.radii sn A

def IsAtomicOverPolydiscNames (B : ParameterBase M) {d m : ℕ}
    (D : Fin d → DC (M := M)) (sn : Fin m → SortTag) (A : Set (Fin m → M)) : Prop :=
  DefinableOverPolydiscNames B D sn A ∧ A.Nonempty ∧
    A ⊆ GammaParameters.sortedUniverse sn ∧
    ∀ C, DefinableOverPolydiscNames B D sn C → A ⊆ C ∨ Disjoint A C

private theorem compose_equiv_inverse {n m : ℕ} (e : Fin n ≃ Fin m) (x : Fin m → M) :
    (x ∘ e) ∘ e.symm = x := by
  funext i
  simp only [Function.comp_apply, e.apply_symm_apply]

private theorem chart_product_image {d : ℕ} {D : Fin d → DC (M := M)}
    (C : PolydiscNaming D) :
    (fun z => z ∘ C.coordinates.symm) ''
      prefixedNamedPolydisc C.points C.closed C.centres C.radii = discNameProduct D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (C.product_iff _).mpr
    have he : (z ∘ C.coordinates.symm) ∘ C.coordinates = z := by
      funext i
      simp only [Function.comp_apply, C.coordinates.symm_apply_apply]
    rwa [he]
  · intro hx
    exact ⟨x ∘ C.coordinates, (C.product_iff x).mp hx,
      compose_equiv_inverse C.coordinates x⟩

private theorem atomic_in_every_chart (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {d : ℕ} (D : Fin d → DC (M := M)) (C : PolydiscNaming D)
    (A : Set (Fin d → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverFiniteDiscNames (tupleBase B (SpecialTransformations.Section4.vfValues C.points))
      C.closed C.centres C.radii (fun _ => .vf) (discNameProduct D) := by
  let A' := (fun x : Fin d → M => x ∘ C.coordinates) '' A
  have hA' : GeneratesCompleteType B (fun _ => .vf) A' := hA.image_real C.coordinates
  have hsub' : prefixedNamedPolydisc C.points C.closed C.centres C.radii ⊆ A' := by
    intro z hz
    let x := z ∘ C.coordinates.symm
    have hzx : x ∘ C.coordinates = z := compose_equiv_inverse C.coordinates.symm z
    have hx : x ∈ discNameProduct D := (C.product_iff x).mpr (hzx.symm ▸ hz)
    exact ⟨x, hsub hx, hzx⟩
  have h := lemma_2_25_singleton_normal_form h00 B hΓ unary gamma
    C.points C.closed C.centres C.radii A' hA' hsub'
  have hp := h.image_equiv C.coordinates.symm
  rwa [chart_product_image C] at hp

/-- Lemma 2.25 for every polydisc admitting finite/singleton charts.
The unary and Gamma results from [18, Section 3] are explicit accepted inputs.
No condition of definability is placed on the containing set A. -/
theorem lemma_2_25 (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {d : ℕ} (D : Fin d → DC (M := M)) (hD : Nonempty (PolydiscNaming D))
    (A : Set (Fin d → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : discNameProduct D ⊆ A) :
    IsAtomicOverPolydiscNames B D (fun _ => .vf) (discNameProduct D) := by
  obtain ⟨C⟩ := hD
  have h := atomic_in_every_chart h00 B hΓ unary gamma D C A hA hsub
  refine ⟨⟨C, h.1⟩, h.2.1, h.2.2.1, ?_⟩
  rintro T ⟨C', hT⟩
  exact (atomic_in_every_chart h00 B hΓ unary gamma D C' A hA hsub).2.2.2 T hT

/-- The full closed-polydisc case of Lemma 2.25, with arbitrary occurrences
of radius infinity. Existence of the name chart is proved, not assumed. -/
theorem lemma_2_25_closed (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {d : ℕ} (a : Fin d → VF M) (γ : Fin d → GammaInfinity M)
    (A : Set (Fin d → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : discNameProduct (fun i => closedDiscCode (a i) (γ i)) ⊆ A) :
    IsAtomicOverPolydiscNames B (fun i => closedDiscCode (a i) (γ i)) (fun _ => .vf)
      (discNameProduct (fun i => closedDiscCode (a i) (γ i))) :=
  lemma_2_25 h00 B hΓ unary gamma _ (closedPolydiscNaming_nonempty a γ) A hA hsub

/-- The full open-polydisc case; all open radii are finite Gamma values. -/
theorem lemma_2_25_open (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {d : ℕ} (a : Fin d → VF M) (δ : Fin d → Gamma M)
    (A : Set (Fin d → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : discNameProduct (finitePolydiscNames (fun _ => false) a δ) ⊆ A) :
    IsAtomicOverPolydiscNames B (finitePolydiscNames (fun _ => false) a δ) (fun _ => .vf)
      (discNameProduct (finitePolydiscNames (fun _ => false) a δ)) :=
  lemma_2_25 h00 B hΓ unary gamma _ ⟨finitePolydiscNaming (fun _ => false) a δ⟩ A hA hsub

end DiamondIntegral.Section2
