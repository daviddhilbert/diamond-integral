import «section 2».DiscTypeFibres
import «section 2».CitedDiscRVImages

/-! Lemma 2.24 with existing finite disc names. The unary step is the
author-accepted [18, Lemma 3.9] in its stated imaginary context. The product
induction and all parameter transport are proved here. No extension of
Corollary 2.21 to arbitrary imaginary ground parameters is asserted. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem append_init_last {n : ℕ} (x : Fin (n+1) → M) :
    Fin.append (Fin.init x) (fun _ : Fin 1 => x (Fin.last n)) = x := by
  rw [Fin.append_right_eq_snoc]
  exact Fin.snoc_init_self x

theorem rectangle_init_projection {n : ℕ} (D : Fin (n+1) → Set M)
    (hne : ({x | ∀ j, x j ∈ D j} : Set (Fin (n+1) → M)).Nonempty) :
    (fun x => x ∘ Fin.castSucc) '' {x | ∀ j, x j ∈ D j} = {x | ∀ j, x j ∈ D j.castSucc} := by
  obtain ⟨b,hb⟩ := hne
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩ j
    exact hy j.castSucc
  · intro hx
    refine ⟨Fin.snoc x (b (Fin.last n)),?_,?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last] using hb (Fin.last n)
      · simpa only [Fin.snoc_castSucc] using hx i
    · funext i
      simp only [Function.comp_apply,Fin.snoc_castSucc]

theorem rectangle_last_fibre {n : ℕ} (D : Fin (n+1) → Set M)
    (x : Fin (n+1) → M) (hx : ∀ j, x j ∈ D j) :
    {z : Fin 1 → M | ∀ j, Fin.append (Fin.init x) z j ∈ D j} = {z | z 0 ∈ D (Fin.last n)} := by
  ext z
  constructor
  · intro hz
    change z 0 ∈ D (Fin.last n)
    simpa only [Fin.append_right_eq_snoc,Fin.snoc_last] using hz (Fin.last n)
  · intro hz j
    change z 0 ∈ D (Fin.last n) at hz
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.append_right_eq_snoc,Fin.snoc_last] using hz
    · simpa only [Fin.append_right_eq_snoc,Fin.snoc_castSucc,Fin.init] using hx i.castSucc

theorem tupleBase_adjoinRV (B : ParameterBase M) {n : ℕ} (u : Fin n → M) (t : RVInfinity M) :
    tupleBase (adjoinRV B t) u = adjoinRV (tupleBase B u) t := by
  simp only [tupleBase,adjoinRV,Set.insert_union]

/-- Unary 2.24 in the prequel's finite disc-parameter context. -/
theorem lemma_2_24_disc_names_unary (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : UnaryOpenDiscRVBaseChangeInput B) {k : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Set M) (hopen : IsOpenDisc D)
    (hD : IsAtomicOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (t : RVInfinity M) :
    IsAtomicOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D} :=
  cited h00 hΓ k closed a δ D hD hopen t

/-- Full finite-product 2.24 over existing finite-radius DC names.
The only cited premise is unary [18, Lemma 3.9]. -/
theorem lemma_2_24_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (cited : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Fin n → Set M) (hopen : ∀ i, IsOpenDisc (D i))
    (hA : IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j})
    (t : RVInfinity M) :
    IsAtomicOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ => .vf) {x | ∀ j, x j ∈ D j} := by
  classical
  induction n generalizing B with
  | zero =>
    refine ⟨hA.1.mono (Set.subset_insert _ _) (Set.Subset.refl _),hA.2.1,hA.2.2.1,?_⟩
    intro C hC
    by_cases hne : ({x : Fin 0 → M | ∀ j, x j ∈ D j} ∩ C).Nonempty
    · obtain ⟨x,hx,hxC⟩ := hne
      exact Or.inl (fun y _ => (Subsingleton.elim x y) ▸ hxC)
    · exact Or.inr (Set.disjoint_left.mpr (fun x hx hxC => hne ⟨x,hx,hxC⟩))
  | succ n ih =>
    let A : Set (Fin (n+1) → M) := {x | ∀ j, x j ∈ D j}
    have hproj := hA.image_real Fin.castSucc
    rw [rectangle_init_projection D hA.2.1] at hproj
    have hhead := ih B hΓ (fun i => D i.castSucc) (fun i => hopen i.castSucc) hproj
    refine ⟨hA.1.mono (Set.subset_insert _ _) (Set.Subset.refl _),hA.2.1,hA.2.2.1,?_⟩
    intro C hC
    let P := (fun x : Fin (n+1) → M => x ∘ Fin.castSucc) '' (C ∩ A)
    have hP : DefinableOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ => .vf) P :=
      (hC.inter (hA.1.mono (Set.subset_insert _ _) (Set.Subset.refl _))).image_real Fin.castSucc
    rcases hhead.2.2.2 P hP with hsub | hdis
    · left
      intro x hx
      have hprefix : ∀ j, Fin.init x j ∈ D j.castSucc := fun j => hx j.castSucc
      obtain ⟨y,⟨hyC,hyA⟩,hyx⟩ := hsub hprefix
      have hsort : Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin 1 => .vf) = (fun _ => .vf) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [Fin.append_right_eq_snoc,Fin.snoc_last,Fin.snoc_castSucc]
      have hAb : IsAtomicOverFiniteDiscNames B closed a δ
          (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin 1 => .vf)) A := by rw [hsort]; exact hA
      have hne : {z : Fin 1 → M | Fin.append (Fin.init x) z ∈ A}.Nonempty :=
        ⟨fun _ => x (Fin.last n),by
          change Fin.append (Fin.init x) (fun _ : Fin 1 => x (Fin.last n)) ∈ A
          rw [append_init_last]
          exact hx⟩
      have hline := hAb.block_fibre hc (Fin.init x) hne
      have heF : {z : Fin 1 → M | Fin.append (Fin.init x) z ∈ A} = {z | z 0 ∈ D (Fin.last n)} :=
        rectangle_last_fibre D x hx
      rw [heF] at hline
      let E := tupleBase B (Fin.init x)
      have hΓE : NontrivialDefinableGamma E := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
      have hlineRV := lemma_2_24_disc_names_unary h00 E hΓE (cited E) closed a δ _ (hopen (Fin.last n)) hline t
      have hCb : DefinableOverFiniteDiscNames (adjoinRV B t) closed a δ
          (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin 1 => .vf)) C := by rw [hsort]; exact hC
      have hCline := (hCb.mono (E := tupleBase (adjoinRV B t) (Fin.init x))
        Set.subset_union_left (Set.Subset.refl _)).fix_prefix (Fin.init x) (fun i => Or.inr (Set.mem_range_self i))
      rw [tupleBase_adjoinRV] at hCline
      have hyreconstruct : Fin.append (Fin.init x) (fun _ : Fin 1 => y (Fin.last n)) = y := by
        have hinit : Fin.init y = Fin.init x := hyx
        rw [← hinit,append_init_last]
      rcases hlineRV.2.2.2 _ hCline with hlast | hlast
      · have h := hlast (show (fun _ : Fin 1 => x (Fin.last n)) ∈ {z : Fin 1 → M | z 0 ∈ D (Fin.last n)} from hx (Fin.last n))
        change Fin.append (Fin.init x) (fun _ : Fin 1 => x (Fin.last n)) ∈ C at h
        simpa only [append_init_last] using h
      · exact (Set.disjoint_left.mp hlast (show (fun _ : Fin 1 => y (Fin.last n)) ∈ {z : Fin 1 → M | z 0 ∈ D (Fin.last n)} from hyA (Fin.last n)) (by
          change Fin.append (Fin.init x) (fun _ : Fin 1 => y (Fin.last n)) ∈ C
          rwa [hyreconstruct])).elim
    · right
      apply Set.disjoint_left.mpr
      intro x hx hxC
      exact Set.disjoint_left.mp hdis (fun j => hx j.castSucc) ⟨x,⟨hxC,hx⟩,rfl⟩

end DiamondIntegral.Section2
