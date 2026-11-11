import «section 2».FiniteChoice

/-! The two compactness steps in Corollary 2.30, at the raw finite-tuple
level. A property of all coded subsets of a complete type locus descends
to a ground-definable neighbourhood, then to a finite definable cover. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] {n m : ℕ}

def rawTypeLocus (S : Set M) (a : Fin n → M) : Set (Fin n → M) :=
  {x | ∀ C : Set (Fin n → M), S.Definable LRV C → a ∈ C → x ∈ C}

theorem mem_rawTypeLocus (S : Set M) (a : Fin n → M) : a ∈ rawTypeLocus S a :=
  fun _ _ ha => ha

theorem rawTypeLocus_decides {S : Set M} (a : Fin n → M)
    (C : Set (Fin n → M)) (hC : S.Definable LRV C) :
    rawTypeLocus S a ⊆ C ∨ Disjoint (rawTypeLocus S a) C := by
  by_cases ha : a ∈ C
  · exact Or.inl (fun _ hx => hx C hC ha)
  · right
    exact Set.disjoint_left.mpr (fun x hx hxC => (hx Cᶜ hC.compl ha) hxC)

def containedFibreCodes (R : (Fin m → M) → Set (Fin n → M)) (C : Set (Fin n → M)) :
    Set (Fin m → M) := {d | R d ⊆ C}

theorem containedFibreCodes_definable {S : Set M}
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : S.Definable LRV {z : Fin m ⊕ Fin n → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (C : Set (Fin n → M)) (hC : S.Definable LRV C) :
    S.Definable LRV (containedFibreCodes R C) := by
  have h := ((hR.inter (hC.preimage_comp Sum.inr).compl).exists_of_finite).compl
  convert h using 1
  ext d
  change (R d ⊆ C) ↔ ¬ ∃ x, x ∈ R d ∧ x ∉ C
  constructor
  · rintro h ⟨x,hx,hno⟩
    exact hno (h hx)
  · intro h x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩

theorem type_local_good_neighbourhood
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A) (a : Fin n → M) (ha : a ∈ A)
    (D P : Set (Fin m → M)) (hD : S.Definable LRV D) (hP : S.Definable LRV P)
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : S.Definable LRV {z : Fin m ⊕ Fin n → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (htype : ∀ d ∈ D, R d ⊆ rawTypeLocus S a → d ∈ P) :
    ∃ C ⊆ A, S.Definable LRV C ∧ a ∈ C ∧ ∀ d ∈ D, R d ⊆ C → d ∈ P := by
  classical
  let Q := {C : Set (Fin n → M) // S.Definable LRV C ∧ a ∈ C}
  let cover (C : Q) := (containedFibreCodes R C.val)ᶜ
  let K := Set.range cover
  have hK : ∀ C ∈ K, S.Definable LRV C := by
    rintro _ ⟨C,rfl⟩
    exact (containedFibreCodes_definable R hR C.val C.property.1).compl
  have hcover : ∀ d ∈ D \ P, ∃ C ∈ K, d ∈ C := by
    rintro d ⟨hd,hnP⟩
    by_contra hn
    apply hnP
    apply htype d hd
    intro x hx C hC haC
    by_contra hxC
    apply hn
    refine ⟨cover ⟨C,hC,haC⟩,Set.mem_range_self _,?_⟩
    exact fun hsub => hxC (hsub hx)
  obtain ⟨K₀,hKf,hKsub,hKcov⟩ := hs.definable_finite_subcover_tuple S hsmall (D \ P)
    (hD.inter hP.compl) K hK hcover
  haveI : Finite K₀ := hKf.to_subtype
  let chooseC (W : K₀) : Q := Classical.choose (hKsub W.property)
  have hchoose (W : K₀) : cover (chooseC W) = W.val := Classical.choose_spec (hKsub W.property)
  let C := A ∩ ⋂ W : K₀, (chooseC W).val
  have hC : S.Definable LRV C := hA.inter
    (Set.definable_iInter_of_finite (fun W : K₀ => (chooseC W).property.1))
  refine ⟨C,Set.inter_subset_left,hC,⟨ha,Set.mem_iInter.mpr (fun W => (chooseC W).property.2)⟩,?_⟩
  intro d hd hsub
  by_contra hnP
  obtain ⟨W,hWK,hdW⟩ := hKcov d ⟨hd,hnP⟩
  let w : K₀ := ⟨W,hWK⟩
  have hno : d ∈ cover (chooseC w) := by rw [hchoose]; exact hdW
  apply hno
  intro x hx
  exact Set.mem_iInter.mp (hsub hx).2 w

theorem type_local_finite_good_cover
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (D P : Set (Fin m → M)) (hD : S.Definable LRV D) (hP : S.Definable LRV P)
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : S.Definable LRV {z : Fin m ⊕ Fin n → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (htype : ∀ a ∈ A, ∀ d ∈ D, R d ⊆ rawTypeLocus S a → d ∈ P) :
    ∃ C : Set (Set (Fin n → M)), C.Finite ∧
      (∀ V ∈ C, V ⊆ A ∧ S.Definable LRV V ∧ ∀ d ∈ D, R d ⊆ V → d ∈ P) ∧
      ∀ a ∈ A, ∃ V ∈ C, a ∈ V := by
  let C := {V : Set (Fin n → M) | V ⊆ A ∧ S.Definable LRV V ∧ ∀ d ∈ D, R d ⊆ V → d ∈ P}
  have hcov : ∀ a ∈ A, ∃ V ∈ C, a ∈ V := by
    intro a ha
    obtain ⟨V,hVA,hV,haV,hgood⟩ := type_local_good_neighbourhood hs S hsmall A hA a ha D P hD hP R hR
      (htype a ha)
    exact ⟨V,⟨hVA,hV,hgood⟩,haV⟩
  obtain ⟨C₀,hCf,hCsub,hCcov⟩ := hs.definable_finite_subcover_tuple S hsmall A hA C
    (fun V hV => hV.2.1) hcov
  exact ⟨C₀,hCf,fun V hV => hCsub hV,hCcov⟩

end DiamondIntegral.Section2
