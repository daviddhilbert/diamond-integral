import «section 2».DiscGroundBridge
import «section 2».AtomicBaseChange

/-!
# Accepted unary and Gamma results from [18, Section 3]

The author explicitly permits taking these results as given while that
section is being formalized. Section 3 of [18] works in the ball-imaginary
expansion. The inputs therefore retain existing finite disc names and may
be replaced if the upstream Lean formulations change. The multivariable
Lemma 2.25 is not an input, and no global logical principle is introduced.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableOverFiniteDiscNames_zero_iff (B : ParameterBase M)
    {m : ℕ} (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    DefinableOverFiniteDiscNames B (Fin.elim0 : Fin 0 → Bool)
      (Fin.elim0 : Fin 0 → VF M) (Fin.elim0 : Fin 0 → Gamma M) sn A ↔
      GammaParameters.DefinableOverBase B sn A := by
  constructor
  · rintro ⟨R, rfl⟩
    have h := R.definable_fibre Fin.elim0 Fin.elim0
    have he : (⟨B.real ∪ Set.range (SpecialTransformations.Section4.vfValues
        (Fin.elim0 : Fin 0 → VF M)),
        B.gamma ∪ Set.range (Fin.elim0 : Fin 0 → Gamma M)⟩ : ParameterBase M) = B := by
      cases B
      congr <;> ext x <;> simp
    rwa [he] at h
  · exact definableOverFiniteDiscNames_of_ground B _ _ _ sn A

theorem generatesTypeOverFiniteDiscNames_zero_iff (B : ParameterBase M)
    {m : ℕ} (sn : Fin m → SortTag) (A : Set (Fin m → M)) :
    GeneratesTypeOverFiniteDiscNames B (Fin.elim0 : Fin 0 → Bool)
      (Fin.elim0 : Fin 0 → VF M) (Fin.elim0 : Fin 0 → Gamma M) sn A ↔
      GeneratesCompleteType B sn A := by
  constructor
  · exact GeneratesTypeOverFiniteDiscNames.ground
  · rintro ⟨hne, hs, ht⟩
    exact ⟨hne, hs, fun C hC => ht C ((definableOverFiniteDiscNames_zero_iff B sn C).mp hC)⟩

/-- Unary [18, Lemma 3.4], including any previously named finite disc tuple.
The source's standing model and nontrivial-ground-value-group hypotheses
are retained. Only a single new VF disc is made atomic. -/
def UnaryDiscAtomicityInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (k : ℕ) (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
      (A : Set (Fin 1 → M)),
      GeneratesTypeOverFiniteDiscNames B closed a δ (fun _ => .vf) A →
      ∀ (isClosed : Bool) (c : VF M) (γ : Gamma M),
        {x : Fin 1 → M | x 0 ∈ BallImaginaries.underlying
          (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)} ⊆ A →
        IsAtomicOverFiniteDiscNames B (Fin.snoc closed isClosed) (Fin.snoc a c) (Fin.snoc δ γ)
          (fun _ : Fin 1 => .vf)
          {x | x 0 ∈ BallImaginaries.underlying
            (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)}

/-- [18, Lemma 3.3] in the same ball-imaginary parameter context.
This is an explicit accepted input, not a proved extension of the narrower
real/Gamma-only interface. Atomicity is required before adjoining Gamma. -/
def AtomicDiscGammaBaseChangeInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (k m : ℕ) (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
      (sn : Fin m → SortTag) (A : Set (Fin m → M)),
      IsAtomicOverFiniteDiscNames B closed a δ sn A → ∀ γ : Gamma M,
        GeneratesTypeOverFiniteDiscNames (adjoinGamma B γ) closed a δ sn A

theorem lemma_2_23_disc_names (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : AtomicDiscGammaBaseChangeInput B) (hΓ : NontrivialDefinableGamma B)
    {k m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ sn A) (γ : Gamma M) :
    IsAtomicOverFiniteDiscNames (adjoinGamma B γ) closed a δ sn A :=
  ⟨hA.1.mono (Set.Subset.refl _) (Set.subset_insert _ _),
    cited h00 hΓ k m closed a δ sn A hA γ⟩

/-- Iterated use of the accepted scalar Gamma result. The finite tuple
adds actual Gamma names, without choosing representatives or disc centres. -/
theorem lemma_2_23_disc_gamma_tuple (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    (hΓ : NontrivialDefinableGamma B) {k m l : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (sn : Fin m → SortTag) (A : Set (Fin m → M))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ sn A) (γ : Fin l → Gamma M) :
    IsAtomicOverFiniteDiscNames ⟨B.real, B.gamma ∪ Set.range γ⟩ closed a δ sn A := by
  classical
  let E (s : Finset (Fin l)) : ParameterBase M :=
    ⟨B.real, B.gamma ∪ γ '' (s : Set (Fin l))⟩
  have hE (s : Finset (Fin l)) : IsAtomicOverFiniteDiscNames (E s) closed a δ sn A := by
    induction s using Finset.induction_on with
    | empty => simpa only [E, Finset.coe_empty, Set.image_empty, Set.union_empty] using hA
    | @insert i s _hi ih =>
      have hΓE : NontrivialDefinableGamma (E s) :=
        hΓ.mono (Set.Subset.refl _) Set.subset_union_left
      have h := lemma_2_23_disc_names h00 (E s) (cited (E s)) hΓE closed a δ sn A ih (γ i)
      simpa only [E, adjoinGamma, Finset.coe_insert, Set.image_insert_eq, Set.union_insert] using h
  simpa only [E, Finset.coe_univ, Set.image_univ] using hE Finset.univ

/-- The unary case of Lemma 2.25 is precisely the accepted cited result.
The general polydisc assertion remains a separate induction to be proved. -/
theorem lemma_2_25_unary (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : UnaryDiscAtomicityInput B) (hΓ : NontrivialDefinableGamma B)
    (A : Set (Fin 1 → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (isClosed : Bool) (c : VF M) (γ : Gamma M)
    (hsub : {x : Fin 1 → M | x 0 ∈ BallImaginaries.underlying
      (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)} ⊆ A) :
    IsAtomicOverFiniteDiscNames B (![isClosed]) (![c]) (![γ]) (fun _ : Fin 1 => .vf)
      {x | x 0 ∈ BallImaginaries.underlying
        (if isClosed then closedDiscCode c γ.val else openDiscCode c γ)} := by
  have h := cited h00 hΓ 0 Fin.elim0 Fin.elim0 Fin.elim0 A
    ((generatesTypeOverFiniteDiscNames_zero_iff B _ A).mpr hA) isClosed c γ hsub
  have he {T : Type} (t : T) : Fin.snoc (Fin.elim0 : Fin 0 → T) t = ![t] := by
    funext i
    fin_cases i
    rfl
  simpa only [he] using h

end DiamondIntegral.Section2
