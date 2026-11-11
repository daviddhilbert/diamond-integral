import «section 2».NamedTypeCompactness

/-! The second compactness step and Boolean partition refinement retain
only the fixed original real and DC parameters. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem named_type_local_finite_good_cover
    {κ : Cardinal} (hs : Saturated M κ) (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    {k n m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) A)
    (D P : Set (Fin m → M))
    (hD : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) D)
    (hP : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) P)
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ : Fin (m+n) => .vf)
      {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd m ∈ R (z ∘ Fin.castAdd n)})
    (htype : ∀ u ∈ A, ∀ d ∈ D, R d ⊆ namedDiscTypeLocus ⟨S,∅⟩ closed a δ u → d ∈ P) :
    ∃ C : Set (Set (Fin n → M)), C.Finite ∧
      (∀ V ∈ C, V ⊆ A ∧ DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) V ∧
        ∀ d ∈ D, R d ⊆ V → d ∈ P) ∧ ∀ u ∈ A, ∃ V ∈ C, u ∈ V := by
  let C := {V : Set (Fin n → M) | V ⊆ A ∧
    DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) V ∧ ∀ d ∈ D, R d ⊆ V → d ∈ P}
  have hcov : ∀ u ∈ A, ∃ V ∈ C, u ∈ V := by
    intro u hu
    obtain ⟨V,hVA,hV,huV,hgood⟩ := named_type_local_good_neighbourhood hs hκ S hsmall closed a δ
      A hA u hu D P hD hP R hR (htype u hu)
    exact ⟨V,⟨hVA,hV,hgood⟩,huV⟩
  obtain ⟨C₀,hCsub,hCf,hCcov⟩ := finite_subcover_disc_names hs hκ S hsmall closed a δ A hA C
    (fun V hV => hV.2.1) hcov
  exact ⟨C₀,hCf,fun V hV => hCsub hV,hCcov⟩

theorem named_finite_good_cover_partition
    (B : ParameterBase M) {k n m : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (A : Set (Fin n → M)) (hA : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) A)
    (D P : Set (Fin m → M)) (R : (Fin m → M) → Set (Fin n → M))
    (C : Set (Set (Fin n → M))) (hCf : C.Finite)
    (hC : ∀ V ∈ C, V ⊆ A ∧ DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) V ∧
      ∀ d ∈ D, R d ⊆ V → d ∈ P)
    (hcover : ∀ u ∈ A, ∃ V ∈ C, u ∈ V) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ A ∧ DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) V ∧
        ∀ d ∈ D, R d ⊆ V → d ∈ P) ∧ ∀ u ∈ A, ∃ V ∈ Q, u ∈ V := by
  classical
  haveI : Finite C := hCf.to_subtype
  let atom (p : C → Bool) : Set (Fin n → M) :=
    {x | x ∈ A ∧ ∀ V : C, decide (x ∈ V.val) = p V}
  have hatom (p : C → Bool) : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (atom p) := by
    let pattern (V : C) : Set (Fin n → M) :=
      if p V then V.val else GammaParameters.sortedUniverse (fun _ => .vf) \ V.val
    have hpat (V : C) : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (pattern V) := by
      cases hp : p V
      · simpa only [pattern,hp,Bool.false_eq_true,ite_false] using (hC V.val V.property).2.1.compl
      · simpa only [pattern,hp,ite_true] using (hC V.val V.property).2.1
    have h := hA.inter (DefinableOverFiniteDiscNames.sorted_finite_iInter pattern hpat)
    convert h using 1
    ext x
    constructor
    · rintro ⟨hx,hxp⟩
      refine ⟨hx,hA.proper hx,?_⟩
      intro V
      have hv := hxp V
      cases hp : p V
      · change x ∈ pattern V
        simp only [pattern,hp,Bool.false_eq_true,ite_false,Set.mem_diff]
        exact ⟨hA.proper hx,by simpa [hp] using hv⟩
      · simpa [pattern,hp] using hv
    · rintro ⟨hx,_,hxp⟩
      refine ⟨hx,?_⟩
      intro V
      have hv := hxp V
      cases hp : p V
      · have hv' : x ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧ x ∉ V.val := by
          simpa only [pattern,hp,Bool.false_eq_true,ite_false,Set.mem_diff] using hv
        simpa [hp] using hv'.2
      · simpa [pattern,hp] using hv
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
  · intro u hu
    let p : C → Bool := fun V => decide (u ∈ V.val)
    have hu' : u ∈ atom p := ⟨hu,fun _ => rfl⟩
    exact ⟨atom p,⟨Set.mem_range_self p,⟨u,hu'⟩⟩,hu'⟩

end DiamondIntegral.Section2
