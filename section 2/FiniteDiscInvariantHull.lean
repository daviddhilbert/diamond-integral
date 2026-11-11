import «section 2».FiniteDiscCodeRows

/-! Saturating a promoted formula over all presentations of the same
finite disc tuple. Promotion can destroy invariance away from the named
real tuple; this definable hull restores it before the tuple is unnamed. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n p m : ℕ}

def discHullCurrent (c : Fin (k+n) → M) (z : Fin (n+(p+m)) → M) : Fin (n+n) → M :=
  Fin.append (z ∘ Fin.castAdd (p+m)) (c ∘ Fin.natAdd k)

def discHullArguments (c : Fin (k+n) → M) (z : Fin (n+(p+m)) → M) (q : Fin (n+n) → M) :
    Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M :=
  Sum.elim (z ∘ Fin.natAdd n ∘ Fin.castAdd m)
    (Sum.elim (Fin.append (c ∘ Fin.castAdd n) (q ∘ Fin.natAdd n))
      (Fin.append (q ∘ Fin.castAdd n) (z ∘ Fin.natAdd n ∘ Fin.natAdd p)))

def discInvariantHull (closed : Fin n → Bool)
    (H : Set (Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M))
    (c : Fin (k+n) → M) (z : Fin (n+(p+m)) → M) : Prop :=
  ∃ q : Fin (n+n) → M, finiteDiscRawEq closed (discHullCurrent c z) q ∧ discHullArguments c z q ∈ H

theorem discInvariantHull_definable (S : Set M) (closed : Fin n → Bool)
    (H : Set (Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M)) (hH : S.Definable LRV H) :
    S.Definable LRV {w : Fin (k+n) ⊕ Fin (n+(p+m)) → M |
      discInvariantHull closed H (w ∘ Sum.inl) (w ∘ Sum.inr)} := by
  let I := Fin (k+n) ⊕ Fin (n+(p+m))
  let W := I ⊕ Fin (n+n)
  let E (w : W → M) : Fin (n+n) ⊕ Fin (n+n) → M :=
    Sum.elim (discHullCurrent (w ∘ Sum.inl ∘ Sum.inl) (w ∘ Sum.inl ∘ Sum.inr)) (w ∘ Sum.inr)
  have hE : S.DefinableMap LRV E := by
    rintro (j | j)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [E,discHullCurrent,Sum.elim_inl,Fin.append_left,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inl (.inr (Fin.castAdd (p+m) i)) : W)))
      · simpa only [E,discHullCurrent,Sum.elim_inl,Fin.append_right,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inl (.inl (Fin.natAdd k i)) : W)))
    · exact Set.DefinableFun.proj LRV
  let A (w : W → M) := discHullArguments (w ∘ Sum.inl ∘ Sum.inl) (w ∘ Sum.inl ∘ Sum.inr) (w ∘ Sum.inr)
  have hA : S.DefinableMap LRV A := by
    rintro (j | j | j)
    · simpa only [A,discHullArguments,Sum.elim_inl,Function.comp_apply] using
        (Set.DefinableFun.proj LRV (i := (Sum.inl (.inr (Fin.natAdd n (Fin.castAdd m j))) : W)))
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [A,discHullArguments,Sum.elim_inr,Sum.elim_inl,Fin.append_left,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inl (.inl (Fin.castAdd n i)) : W)))
      · simpa only [A,discHullArguments,Sum.elim_inr,Sum.elim_inl,Fin.append_right,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inr (Fin.natAdd n i) : W)))
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [A,discHullArguments,Sum.elim_inr,Fin.append_left,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inr (Fin.castAdd n i) : W)))
      · simpa only [A,discHullArguments,Sum.elim_inr,Fin.append_right,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inl (.inr (Fin.natAdd n (Fin.natAdd p i))) : W)))
  exact (((finiteDiscRawEq_definable S closed).preimage_map hE).inter (hH.preimage_map hA)).exists_of_finite

theorem discHullCurrent_append (c : Fin (k+n) → M) (a : Fin n → VF M) (x : Fin (p+m) → M) :
    discHullCurrent c (Fin.append (vfValues a) x) = Fin.append (vfValues a) (c ∘ Fin.natAdd k) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [discHullCurrent,Fin.append_left,Function.comp_apply]
  · simp only [discHullCurrent,Fin.append_right,Function.comp_apply]

theorem discHullArguments_append (c : Fin (k+n) → M) (a : Fin n → VF M)
    (u : Fin p → M) (x : Fin m → M) (q : Fin (n+n) → M) :
    discHullArguments c (Fin.append (vfValues a) (Fin.append u x)) q =
      Sum.elim u (Sum.elim (Fin.append (c ∘ Fin.castAdd n) (q ∘ Fin.natAdd n))
        (Fin.append (q ∘ Fin.castAdd n) x)) := by
  funext j
  rcases j with j | j | j
  · simp only [discHullArguments,Sum.elim_inl,Function.comp_apply,Fin.append_right,Fin.append_left]
  · rfl
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [discHullArguments,Sum.elim_inr,Fin.append_left,Function.comp_apply]
    · simp only [discHullArguments,Sum.elim_inr,Function.comp_apply,Fin.append_right]

end DiamondIntegral.Section2
