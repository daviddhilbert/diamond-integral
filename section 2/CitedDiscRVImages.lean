import «section 2».CitedDiscAtomicity
import «section 2».CitedUnaryImages
import «section 2».RVImage

/-! Unary results from [18, Section 3] in its stated ball-imaginary context.
These replaceable inputs retain every finite DC ground name. Lemma 3.9's
set-valued RV constancy is used in its atomicity-after-an-RV-name form;
Lemma 3.13 supplies only the unary nonconstant-image geometry. The product
and compactness steps of Corollary 2.30 are not inputs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The atomicity formulation of [18, Lemma 3.9] for a unary atomic open
disc. A formula with one additional RV name has a set-valued RV row map;
constancy of that map says that the formula is constant on the disc.
Existing DC names remain fixed throughout. -/
def UnaryOpenDiscRVBaseChangeInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (k : ℕ) (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
      (D : Set M),
      IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D} →
      IsOpenDisc D → ∀ t : RVInfinity M,
      IsAtomicOverFiniteDiscNames (adjoinRV B t) closed a δ
        (fun _ : Fin 1 => .vf) {z | z 0 ∈ D}

/-- The geometric conclusion of unary [18, Lemma 3.13], with any existing
finite disc prefix. It does not assert a multivariable image theorem. -/
def OpenDiscNamesImageInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (k : ℕ) (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
      (D : Set M) (f : M → M),
      IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D} →
      IsOpenDisc D →
      DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin 2 => .vf) (scalarVFGraph D f) →
      (¬ ∃ c : M, ∀ x ∈ D, f x = c) → IsOpenDisc (f '' D)

/-- Unary RV-row constancy over the retained actual disc names. No finite
or nonempty row assumption is required, and the zero RV tag is included. -/
theorem named_open_disc_rv_rows_constant (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : UnaryOpenDiscRVBaseChangeInput B)
    {k : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Set M)
    (hD : IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (hopen : IsOpenDisc D) (R : Set ((Fin 1 → M) × M))
    (hR : GammaParameters.DefinableOverBase B (Fin.lastCases .rv (fun _ : Fin 1 => .vf))
      {z | (Fin.init z,z (Fin.last 1)) ∈ R}) :
    ∀ p : Fin 1 → M, p 0 ∈ D → ∀ q : Fin 1 → M, q 0 ∈ D →
      ∀ t, (p,t) ∈ R ↔ (q,t) ∈ R := by
  have hstep (p q : Fin 1 → M) (hp : p 0 ∈ D) (hq : q 0 ∈ D)
      (t : M) (hpt : (p,t) ∈ R) : (q,t) ∈ R := by
    have hpR : (Fin.snoc p t : Fin 2 → M) ∈ {z : Fin 2 → M | (Fin.init z,z (Fin.last 1)) ∈ R} := by
      simpa only [Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last] using hpt
    have hs := hR.proper (Fin.snoc p t) hpR (Fin.last 1)
    have ht : iRV t := by simpa only [Fin.snoc_last,Fin.lastCases_last,sortEval,iRV] using hs
    let tag : RVInfinity M := ⟨t,ht⟩
    have hAt := cited h00 hΓ k closed a δ D hD hopen tag
    have hC := definableOverFiniteDiscNames_of_ground (adjoinRV B tag) closed a δ
      (fun _ : Fin 1 => .vf) {x | (x,t) ∈ R} (rv_row_definable B R hR tag)
    rcases hAt.2.2.2 _ hC with hsub | hdis
    · exact hsub hq
    · exact (Set.disjoint_left.mp hdis hp hpt).elim
  intro p hp q hq t
  exact ⟨hstep p q hp hq t,hstep q p hq hp t⟩

/-- The unary image dichotomy over finite DC names. The constant case is
proved directly; only the nonconstant unary case uses the cited input. -/
theorem named_open_disc_image (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : OpenDiscNamesImageInput B)
    {k : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Set M) (f : M → M)
    (hD : IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (hopen : IsOpenDisc D)
    (hG : DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin 2 => .vf) (scalarVFGraph D f)) :
    (f '' D).Subsingleton ∨ IsOpenDisc (f '' D) := by
  by_cases hc : ∃ c : M, ∀ x ∈ D, f x = c
  · obtain ⟨c,hc⟩ := hc
    left
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hc x hx).trans (hc y hy).symm
  · exact Or.inr (cited h00 hΓ k closed a δ D f hD hopen hG hc)

end DiamondIntegral.Section2
