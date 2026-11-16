import «section 6».NormalizedProtectedFocusGraphs

/-! First-order tests involving two complete graph entries. In
particular, independence of the active VF coordinate is a definable
condition on a focus-graph template's parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ : Type} [Finite ι] [Finite τ]

def binaryGraphConditionLocus (R : Set (ι ⊕ τ → M))
    (C : Set (ι ⊕ (τ ⊕ τ) → M)) : Set (ι → M) :=
  {t | ∀ x y,Sum.elim t x ∈ R → Sum.elim t y ∈ R → Sum.elim t (Sum.elim x y) ∈ C}

theorem binaryGraphConditionLocus_definable (R : Set (ι ⊕ τ → M))
    (C : Set (ι ⊕ (τ ⊕ τ) → M))
    (hR : S.Definable LRV R) (hC : S.Definable LRV C) :
    S.Definable LRV (binaryGraphConditionLocus R C) := by
  let left : ι ⊕ τ → (ι ⊕ τ) ⊕ τ := Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)
  let right : ι ⊕ τ → (ι ⊕ τ) ⊕ τ := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let both : ι ⊕ (τ ⊕ τ) → (ι ⊕ τ) ⊕ τ :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  have hBad := ((hR.preimage_comp left).inter (hR.preimage_comp right)).inter
    (hC.preimage_comp both).compl
  convert (hBad.exists_of_finite.exists_of_finite).compl using 1
  ext t
  have hl (x y : τ → M) : Sum.elim (Sum.elim t x) y ∘ left=Sum.elim t x := by
    funext i; cases i <;> rfl
  have hr (x y : τ → M) : Sum.elim (Sum.elim t x) y ∘ right=Sum.elim t y := by
    funext i; cases i <;> rfl
  have hb (x y : τ → M) : Sum.elim (Sum.elim t x) y ∘ both=Sum.elim t (Sum.elim x y) := by
    funext i; rcases i with i | (i | i) <;> rfl
  change (∀ x y,Sum.elim t x ∈ R → Sum.elim t y ∈ R → Sum.elim t (Sum.elim x y) ∈ C) ↔
    ¬ ∃ x y : τ → M,(Sum.elim (Sum.elim t x) y ∘ left ∈ R ∧
      Sum.elim (Sum.elim t x) y ∘ right ∈ R) ∧ Sum.elim (Sum.elim t x) y ∘ both ∉ C
  simp only [hl,hr,hb,not_exists,not_and,not_not]
  constructor
  · intro h x y hxy
    exact h x y hxy.1 hxy.2
  · intro h x y hx hy
    exact h x y ⟨hx,hy⟩

variable {n r : ℕ}

def focusIndependenceCondition (ι : Type) (j : Fin n) :
    Set (ι ⊕ (((Fin n ⊕ Fin r) ⊕ Fin 1) ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1)) → M) :=
  {z | (∀ k : Fin r,z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))) →
    (∀ i : Fin n,i ≠ j → z (.inr (.inl (.inl (.inl i))))=z (.inr (.inr (.inl (.inl i))))) →
      z (.inr (.inl (.inr 0)))=z (.inr (.inr (.inr 0)))}

theorem focusIndependenceCondition_definable (j : Fin n) :
    S.Definable LRV (focusIndependenceCondition (M := M) ι (r := r) j) := by
  let Z := ι ⊕ (((Fin n ⊕ Fin r) ⊕ Fin 1) ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1))
  have hRV (k : Fin r) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hVF (i : {i : Fin n // i ≠ j}) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inl (.inl i.val))))=z (.inr (.inr (.inl (.inl i.val))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hOut : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr 0)))=z (.inr (.inr (.inr 0)))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  convert ((Set.definable_iInter_of_finite hRV).inter
    (Set.definable_iInter_of_finite hVF)).compl.union hOut using 1
  ext z
  simp only [focusIndependenceCondition,Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,
    Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hRV : ∀ k : Fin r,z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))
    · by_cases hVF : ∀ i : Fin n,i ≠ j →
          z (.inr (.inl (.inl (.inl i))))=z (.inr (.inr (.inl (.inl i))))
      · exact Or.inr (h hRV hVF)
      · exact Or.inl (fun hPair => hVF (fun i hi => hPair.2 ⟨i,hi⟩))
    · exact Or.inl (fun hPair => hRV hPair.1)
  · intro h hRV hVF
    rcases h with h | h
    · exact False.elim (h ⟨hRV,fun i => hVF i.val i.property⟩)
    · exact h

def focusIndependentParameterLocus (R : Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M))
    (j : Fin n) : Set (ι → M) := binaryGraphConditionLocus R (focusIndependenceCondition ι j)

theorem focusIndependentParameterLocus_definable
    (R : Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable LRV (focusIndependentParameterLocus R j) :=
  binaryGraphConditionLocus_definable R _ hR (focusIndependenceCondition_definable j)

end DiamondIntegral.Section6
