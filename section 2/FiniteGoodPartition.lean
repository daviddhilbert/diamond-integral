import «section 2».TypeLocalCompactness

/-! Finite Boolean refinement of the compactness cover in Corollary 2.30.
Only nonempty atoms are retained. A condition on every coded subset of
a cover member descends to each partition piece. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n m : ℕ}

theorem finite_good_cover_partition (S : Set M) (A : Set (Fin n → M))
    (hA : S.Definable LRV A) (D P : Set (Fin m → M))
    (R : (Fin m → M) → Set (Fin n → M))
    (C : Set (Set (Fin n → M))) (hCf : C.Finite)
    (hC : ∀ V ∈ C, V ⊆ A ∧ S.Definable LRV V ∧ ∀ d ∈ D, R d ⊆ V → d ∈ P)
    (hcover : ∀ a ∈ A, ∃ V ∈ C, a ∈ V) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ S.Definable LRV V ∧
        ∀ d ∈ D, R d ⊆ V → d ∈ P) ∧ ∀ a ∈ A, ∃ V ∈ Q, a ∈ V := by
  classical
  haveI : Finite C := hCf.to_subtype
  let atom (p : C → Bool) : Set (Fin n → M) :=
    {x | x ∈ A ∧ ∀ V : C, decide (x ∈ V.val) = p V}
  have hatom (p : C → Bool) : S.Definable LRV (atom p) := by
    have hV (V : C) : S.Definable LRV
        {x : Fin n → M | decide (x ∈ V.val) = p V} := by
      cases hp : p V
      · convert (hC V.val V.property).2.1.compl using 1
        ext x
        simp [hp]
      · convert (hC V.val V.property).2.1 using 1
        ext x
        simp [hp]
    convert hA.inter (Set.definable_iInter_of_finite hV) using 1
    ext x
    simp only [atom, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  let Q := {V : Set (Fin n → M) | V ∈ Set.range atom ∧ V.Nonempty}
  have hQf : Q.Finite := (Set.finite_range atom).subset (fun _ h => h.1)
  refine ⟨Q,hQf,?_,?_,?_⟩
  · rintro U ⟨⟨p,rfl⟩,_⟩ V ⟨⟨q,rfl⟩,_⟩ hne
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    apply hne
    congr 1
    funext W
    exact (hxp.2 W).symm.trans (hxq.2 W)
  · rintro V ⟨⟨p,rfl⟩,hne⟩
    obtain ⟨x,hx⟩ := hne
    obtain ⟨W,hWC,hxW⟩ := hcover x hx.1
    have hsub : atom p ⊆ W := by
      intro y hy
      have he : decide (y ∈ W) = decide (x ∈ W) :=
        (hy.2 ⟨W,hWC⟩).trans (hx.2 ⟨W,hWC⟩).symm
      exact of_decide_eq_true (he.trans (by simp [hxW]))
    exact ⟨⟨x,hx⟩,fun _ h => h.1,hatom p,fun d hd h =>
      (hC W hWC).2.2 d hd (h.trans hsub)⟩
  · intro a ha
    let p : C → Bool := fun V => decide (a ∈ V.val)
    have ha' : a ∈ atom p := ⟨ha,fun _ => rfl⟩
    exact ⟨atom p,⟨Set.mem_range_self p,⟨a,ha'⟩⟩,ha'⟩

theorem type_local_finite_good_partition
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (D P : Set (Fin m → M)) (hD : S.Definable LRV D) (hP : S.Definable LRV P)
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : S.Definable LRV {z : Fin m ⊕ Fin n → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (htype : ∀ a ∈ A, ∀ d ∈ D, R d ⊆ rawTypeLocus S a → d ∈ P) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ S.Definable LRV V ∧
        ∀ d ∈ D, R d ⊆ V → d ∈ P) ∧ ∀ a ∈ A, ∃ V ∈ Q, a ∈ V := by
  obtain ⟨C,hCf,hC,hcov⟩ := type_local_finite_good_cover hs S hsmall A hA D P hD hP R hR htype
  exact finite_good_cover_partition S A hA D P R C hCf hC hcov

end DiamondIntegral.Section2
