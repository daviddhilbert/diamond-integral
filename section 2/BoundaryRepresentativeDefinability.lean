import «section 2».BoundaryRepresentativeValues

/-! Full original-base graphs of the representative correspondence,
including its singleton-zero value when the unary boundary is empty. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem boundaryRepresentativeCandidates_definable (S : Set M)
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ coordinateBoundaryPairs A i ∧ f (z ∘ Sum.inl) = z (.inr 0)}) :
    S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
      z (.inr 0) ∈ boundaryRepresentativeCandidates A i f (z ∘ Sum.inl)} := by
  let idx : Fin n ⊕ Fin 1 → Fin (n+1) ⊕ Fin 1 := Sum.map Fin.castSucc id
  convert hf.image_comp idx using 1
  ext z
  constructor
  · rintro ⟨t,ht,hfy⟩
    let w : Fin (n+1) ⊕ Fin 1 → M :=
      Sum.elim (Fin.snoc (z ∘ Sum.inl) t.val) (fun _ => z (.inr 0))
    refine ⟨w,⟨ht,hfy⟩,?_⟩
    funext j
    cases j with
    | inl j => simp only [w,idx,Function.comp_apply,Sum.map_inl,Sum.elim_inl,Fin.snoc_castSucc]
    | inr j => fin_cases j; rfl
  · rintro ⟨w,⟨hp,hfw⟩,hw⟩
    let p : Fin (n+1) → M := w ∘ Sum.inl
    change p ∈ coordinateBoundaryPairs A i at hp
    have htRV : iRV (p (Fin.last n)) := by
      simpa only [boundaryParameterSort,Fin.lastCases_last,sortEval,iRV] using hp.1 (Fin.last n)
    let t : RVInfinity M := ⟨p (Fin.last n),htRV⟩
    have ha : Fin.init p = z ∘ Sum.inl := by
      funext j
      exact congrFun hw (.inl j)
    have hpar : Fin.snoc (z ∘ Sum.inl) t.val = p := by
      rw [← ha]
      exact Fin.snoc_init_self p
    refine ⟨t,?_,?_⟩
    · change Fin.snoc (z ∘ Sum.inl) t.val ∈ coordinateBoundaryPairs A i
      rwa [hpar]
    · change f (Fin.snoc (z ∘ Sum.inl) t.val) = z (.inr 0)
      rw [hpar]
      exact hfw.trans (congrFun hw (.inr 0))

theorem boundaryRepresentativeValues_raw_definable (S : Set M) (D : Set (Fin n → M))
    (hD : S.Definable LRV D) (A : Set (Fin (n+1) → M)) (i : Fin (n+1))
    (f : (Fin (n+1) → M) → M)
    (hf : S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ coordinateBoundaryPairs A i ∧ f (z ∘ Sum.inl) = z (.inr 0)}) :
    S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ D ∧ z (.inr 0) ∈ boundaryRepresentativeValues A i f (z ∘ Sum.inl)} := by
  classical
  have hC := boundaryRepresentativeCandidates_definable S A i f hf
  have hDom : S.Definable LRV {a : Fin n → M | (boundaryRepresentativeCandidates A i f a).Nonempty} := by
    convert hC.exists_of_finite using 1
    ext a
    change (boundaryRepresentativeCandidates A i f a).Nonempty ↔
      ∃ y : Fin 1 → M, y 0 ∈ boundaryRepresentativeCandidates A i f a
    exact ⟨fun ⟨y,hy⟩ => ⟨fun _ => y,hy⟩,fun ⟨y,hy⟩ => ⟨y 0,hy⟩⟩
  have hzero : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin 1 → M => (0 : VF M).val) :=
    SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0
        (fun j => j.elim0))
  have hZ := (Set.DefinableFun.proj LRV (i := (Sum.inr 0 : Fin n ⊕ Fin 1))).ofPred_eq hzero
  convert (hD.preimage_comp Sum.inl).inter
    (hC.union (((hDom.preimage_comp Sum.inl).compl).inter hZ)) using 1
  ext z
  change (z ∘ Sum.inl ∈ D ∧ z (.inr 0) ∈ boundaryRepresentativeValues A i f (z ∘ Sum.inl)) ↔
    (z ∘ Sum.inl ∈ D ∧ (z (.inr 0) ∈ boundaryRepresentativeCandidates A i f (z ∘ Sum.inl) ∨
      (¬ (boundaryRepresentativeCandidates A i f (z ∘ Sum.inl)).Nonempty ∧ z (.inr 0) = (0 : VF M).val)))
  by_cases h : (boundaryRepresentativeCandidates A i f (z ∘ Sum.inl)).Nonempty
  · simp only [boundaryRepresentativeValues,h,ite_true,not_true_eq_false,false_and,or_false]
  · have hno : z (.inr 0) ∉ boundaryRepresentativeCandidates A i f (z ∘ Sum.inl) := fun hz => h ⟨_,hz⟩
    simp only [boundaryRepresentativeValues,Set.mem_singleton_iff,hno,h,ite_false,
      not_false_eq_true,false_or,true_and]

theorem boundaryRepresentativeValues_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (D : Set (Fin n → M)) (hD : DefinableOver S (fun _ => .vf) D)
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ coordinateBoundaryPairs A i ∧ f (z ∘ Sum.inl) = z (.inr 0)})
    (hgood : ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n)) :
    DefinableOver S (fun _ : Fin (n+1) => .vf)
      {z | Fin.init z ∈ D ∧ z (Fin.last n) ∈ boundaryRepresentativeValues A i f (Fin.init z)} := by
  have hsort : D ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hD
    exact fun _ hz => hz.1
  have hraw := boundaryRepresentativeValues_raw_definable S D hD.raw_definable A i f hf
  let idx : Fin n ⊕ Fin 1 → Fin (n+1) := Sum.elim Fin.castSucc (fun _ => Fin.last n)
  apply raw_definableOver_sorted hc
  · convert hraw.preimage_comp idx using 1
    ext z
    rfl
  · rintro z ⟨hzD,hzy⟩ j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · exact boundaryRepresentativeValues_proper A i f hgood (Fin.init z) hzy
    · exact hsort hzD q

theorem boundary_representative_correspondence_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin (n+1) → M)) (hA : DefinableOver S (fun _ => .vf) A) (i : Fin (n+1))
    (D : Set (Fin n → M)) (hD : DefinableOver S (fun _ => .vf) D) :
    ∃ F : (Fin n → M) → Set M,
      DefinableOver S (fun _ : Fin (n+1) => .vf) {z | Fin.init z ∈ D ∧ z (Fin.last n) ∈ F (Fin.init z)} ∧
      ∀ a ∈ D, (F a).Finite ∧ Set.InjOn iRv (F a) ∧
        Subtype.val '' boundaryTagSet A i a ⊆ iRv '' F a := by
  obtain ⟨f,hf,hgood⟩ := uniform_coordinate_boundary_representatives h00 hs S hsmall A hA i
  have hsort : D ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hD
    exact fun _ hz => hz.1
  have hAB := (GammaParameters.base_empty_iff S (fun _ => .vf) A).mpr hA
  refine ⟨boundaryRepresentativeValues A i f,
    boundaryRepresentativeValues_definable hc S D hD A i f hf hgood,?_⟩
  intro a ha
  exact ⟨boundaryRepresentativeValues_finite ⟨S,∅⟩ A hAB i f a (hsort ha),
    boundaryRepresentativeValues_rv_injective A i f hgood a,
    boundaryTagSet_subset_representative_rv_image A i f hgood a⟩

end DiamondIntegral.Section2
