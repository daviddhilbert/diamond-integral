import «section 5».OriginalParameterFreeFormulas
import IntegrationSection6.GammaFamilyQuantifiers

/-! Boolean operations, coordinate substitution, and sorted quantifiers
preserve genuine original-Gamma definability. No raw Gamma names are added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ} {s : Fin n → SortTag} {t : Fin m → SortTag}

def OriginalSortedPredicate (B : Base (M := M)) {n : ℕ} (s : Fin n → SortTag)
    (P : (Fin n → M) → Prop) : Prop :=
  DefinableOverBase B s {x | x ∈ sortedUniverse s ∧ P x}

variable {P Q : (Fin n → M) → Prop}

theorem OriginalSortedPredicate.of_definable {D : Set (Fin n → M)} (hD : DefinableOverBase B s D) :
    OriginalSortedPredicate B s (fun x => x ∈ D) := by
  unfold OriginalSortedPredicate
  convert hD using 1
  ext x
  exact and_iff_right_iff_imp.mpr (hD.proper x)

theorem OriginalSortedPredicate.truth : OriginalSortedPredicate B s (fun _ => True) := by
  unfold OriginalSortedPredicate
  simpa only [and_true, Set.setOf_mem_eq] using
    real_definableOverBase B s (sortedUniverse s) (sortedUniverse_definable B.real s)

theorem OriginalSortedPredicate.neg (hP : OriginalSortedPredicate B s P) :
    OriginalSortedPredicate B s (fun x => ¬ P x) := by
  unfold OriginalSortedPredicate at *
  have h := hP.compl
  convert h using 1
  ext x
  change (_ ∧ ¬ P x) ↔ (_ ∧ ¬ (_ ∧ P x))
  tauto

theorem OriginalSortedPredicate.conj (hP : OriginalSortedPredicate B s P) (hQ : OriginalSortedPredicate B s Q) :
    OriginalSortedPredicate B s (fun x => P x ∧ Q x) := by
  unfold OriginalSortedPredicate at *
  have h := hP.inter hQ
  convert h using 1
  ext x
  change (_ ∧ (P x ∧ Q x)) ↔ ((_ ∧ P x) ∧ (_ ∧ Q x))
  tauto

theorem OriginalSortedPredicate.disj (hP : OriginalSortedPredicate B s P) (hQ : OriginalSortedPredicate B s Q) :
    OriginalSortedPredicate B s (fun x => P x ∨ Q x) := by
  unfold OriginalSortedPredicate at *
  have h := hP.union hQ
  convert h using 1
  ext x
  change (_ ∧ (P x ∨ Q x)) ↔ ((_ ∧ P x) ∨ (_ ∧ Q x))
  tauto

theorem OriginalSortedPredicate.impl (hP : OriginalSortedPredicate B s P) (hQ : OriginalSortedPredicate B s Q) :
    OriginalSortedPredicate B s (fun x => P x → Q x) := by
  simpa only [imp_iff_not_or] using hP.neg.disj hQ

theorem OriginalSortedPredicate.iff (hP : OriginalSortedPredicate B s P) (hQ : OriginalSortedPredicate B s Q) :
    OriginalSortedPredicate B s (fun x => P x ↔ Q x) := by
  simpa only [iff_iff_implies_and_implies] using (hP.impl hQ).conj (hQ.impl hP)

theorem OriginalSortedPredicate.congr (hP : OriginalSortedPredicate B s P)
    (h : ∀ x, x ∈ sortedUniverse s → (P x ↔ Q x)) : OriginalSortedPredicate B s Q := by
  unfold OriginalSortedPredicate at *
  convert hP using 1
  ext x
  exact and_congr_right (fun hx => (h x hx).symm)

theorem OriginalSortedPredicate.pullback (hP : OriginalSortedPredicate B s P) (f : Fin n → Fin m)
    (hf : ∀ i, s i = t (f i)) :
    OriginalSortedPredicate B t (fun x => P (x ∘ f)) := by
  unfold OriginalSortedPredicate at *
  have h := hP.preimage_real t f
  convert h using 1
  ext x
  change (_ ∧ P (x ∘ f)) ↔ ((_ ∧ P (x ∘ f)) ∧ _)
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨⟨fun i => hf i ▸ hx (f i), hp⟩, hx⟩
  · rintro ⟨⟨_, hp⟩, hx⟩
    exact ⟨hx, hp⟩

theorem OriginalSortedPredicate.all {R : (Fin (n+m) → M) → Prop}
    (hR : OriginalSortedPredicate B (Fin.append s t) R) :
    OriginalSortedPredicate B s (fun x => ∀ y : Fin m → M,
      y ∈ sortedUniverse t → R (Fin.append x y)) := by
  unfold OriginalSortedPredicate at *
  have h := gamma_family_row_forall_definable s t hR
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy => ⟨?_, hall y hy⟩⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hx j
    · simpa only [Fin.append_right] using hy j
  · rintro ⟨hx, hall⟩
    exact ⟨hx, fun y hy => (hall y hy).2⟩

theorem OriginalSortedPredicate.ex {R : (Fin (n+m) → M) → Prop}
    (hR : OriginalSortedPredicate B (Fin.append s t) R) :
    OriginalSortedPredicate B s (fun x => ∃ y : Fin m → M,
      y ∈ sortedUniverse t ∧ R (Fin.append x y)) := by
  unfold OriginalSortedPredicate at *
  have h := gamma_family_row_exists_definable s t hR
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, y, hy, hr⟩
    refine ⟨y, ?_, hr⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hx j
    · simpa only [Fin.append_right] using hy j
  · rintro ⟨y, hs, hr⟩
    exact ⟨(fun i => by simpa only [Fin.append_left] using hs (Fin.castAdd m i)),
      y, (fun j => by simpa only [Fin.append_right] using hs (Fin.natAdd n j)), hr⟩

theorem OriginalSortedPredicate.finite_all {ι : Type} [Fintype ι] {P : ι → (Fin n → M) → Prop}
    (hP : ∀ i, OriginalSortedPredicate B s (P i)) :
    OriginalSortedPredicate B s (fun x => ∀ i, P i x) := by
  have hn : OriginalSortedPredicate B s (fun x => ∃ i, ¬ P i x) := by
    unfold OriginalSortedPredicate
    have h := DefinableOverBase.finite_iUnion Finset.univ (fun i => {x | x ∈ sortedUniverse s ∧ ¬ P i x})
      (fun i _ => (hP i).neg)
    convert h using 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨hx, i, hi⟩
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, hi⟩
      exact ⟨hx, i, hi⟩
  simpa only [not_exists, not_not] using hn.neg

end DiamondIntegral.Section5
