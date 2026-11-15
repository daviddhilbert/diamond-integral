import «section 5».RESSetOperations

/-! Finite disjoint partitions of literal original-base RV domains are
additive in the actual native ungraded RES ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvFiniteUnion {S : Set M} {n : ℕ} {I : Type} (s : Finset I)
    (D : I → DefSet (rawRVSpace (M := M) n) S) : DefSet (rawRVSpace (M := M) n) S where
  carrier := s.sup (fun i => (D i).carrier)
  definable := by
    induction s using Finset.induction_on with
    | empty => exact Space.definable_empty _ S
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact Space.Definable.union _ (D i).definable ih

theorem rvFiniteUnion_mem {S : Set M} {n : ℕ} {I : Type} (s : Finset I)
    (D : I → DefSet (rawRVSpace (M := M) n) S) (r : Fin n → CanonicalRV.RVSort M) :
    r ∈ (rvFiniteUnion s D).carrier ↔ ∃ i ∈ s, r ∈ (D i).carrier := by
  change r ∈ s.sup (fun i => (D i).carrier) ↔ _
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert, Set.sup_eq_union, Set.mem_union, ih, Finset.mem_insert]
    constructor
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact ⟨i, Or.inl rfl, hx⟩
      · exact ⟨j, Or.inr hj, hx⟩
    · rintro ⟨j, hj | hj, hx⟩
      · subst j; exact Or.inl hx
      · exact Or.inr ⟨j, hj, hx⟩

theorem rvFiniteUnion_finite_values {S : Set M} {n : ℕ} {I : Type} (s : Finset I)
    (D : I → DefSet (rawRVSpace (M := M) n) S)
    (hD : ∀ i, (Set.range (fun u : D i => fun j => Values.vrv (u.val j))).Finite) :
    (Set.range (fun u : rvFiniteUnion s D => fun j => Values.vrv (u.val j))).Finite := by
  induction s using Finset.induction_on with
  | empty =>
    apply Set.finite_empty.subset
    rintro p ⟨u, _⟩
    exact u.property.elim
  | @insert i s hi ih =>
    apply ((hD i).union ih).subset
    rintro p ⟨u, rfl⟩
    obtain ⟨j, hj, hu⟩ := (rvFiniteUnion_mem (insert i s) D u.val).mp u.property
    rcases Finset.mem_insert.mp hj with he | hj
    · subst j
      exact Or.inl ⟨⟨u.val, hu⟩, rfl⟩
    · exact Or.inr ⟨⟨u.val, (rvFiniteUnion_mem s D u.val).mpr ⟨j, hj, hu⟩⟩, rfl⟩

theorem resSetClass_disjoint_union (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A B C : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (hC : (Set.range (fun u : C => fun i => Values.vrv (u.val i))).Finite)
    (hd : Disjoint A.carrier B.carrier) (he : C.carrier = A.carrier ∪ B.carrier) :
    resSetClass hc C hC = resSetClass hc A hA + resSetClass hc B hB := by
  apply resSetClass_scissor
  · rw [he]; exact Set.subset_union_left
  · rw [he]
    ext r
    constructor
    · intro hr
      exact ⟨Or.inr hr, fun ha => Set.disjoint_left.mp hd ha hr⟩
    · rintro ⟨hr, hn⟩
      exact hr.resolve_left hn

theorem resSetClass_finiteUnion (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} {I : Type} (s : Finset I)
    (D : I → DefSet (rawRVSpace (M := M) n) S)
    (hD : ∀ i, (Set.range (fun u : D i => fun j => Values.vrv (u.val j))).Finite)
    (hd : Set.PairwiseDisjoint (s : Set I) (fun i => (D i).carrier)) :
    resSetClass hc (rvFiniteUnion s D) (rvFiniteUnion_finite_values s D hD) =
      ∑ i ∈ s, resSetClass hc (D i) (hD i) := by
  induction s using Finset.induction_on with
  | empty => exact resSetClass_empty hc _ _ rfl
  | @insert i s hi ih =>
    have hdis : Disjoint (D i).carrier (rvFiniteUnion s D).carrier := by
      apply Set.disjoint_left.mpr
      intro r hr hs
      obtain ⟨j, hj, hrj⟩ := (rvFiniteUnion_mem s D r).mp hs
      exact Set.disjoint_left.mp (hd (by simp) (by simp [hj]) (by intro he; exact hi (he ▸ hj))) hr hrj
    have hrest : Set.PairwiseDisjoint (s : Set I) (fun i => (D i).carrier) :=
      fun j hj k hk hjk => hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
    have he : (rvFiniteUnion (insert i s) D).carrier = (D i).carrier ∪ (rvFiniteUnion s D).carrier :=
      Finset.sup_insert (f := fun j => (D j).carrier)
    have hsplit := resSetClass_disjoint_union hc (D i) (rvFiniteUnion s D)
      (rvFiniteUnion (insert i s) D) (hD i) (rvFiniteUnion_finite_values s D hD)
      (rvFiniteUnion_finite_values (insert i s) D hD) hdis he
    rw [hsplit, ih hrest, Finset.sum_insert hi]

theorem resSetClass_finite_partition (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} {I : Type} [Fintype I]
    (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun j => Values.vrv (u.val j))).Finite)
    (D : I → DefSet (rawRVSpace (M := M) n) S)
    (hD : ∀ i, (Set.range (fun u : D i => fun j => Values.vrv (u.val j))).Finite)
    (hd : Pairwise (fun i j => Disjoint (D i).carrier (D j).carrier))
    (hcovers : ∀ r, r ∈ A.carrier ↔ ∃ i, r ∈ (D i).carrier) :
    resSetClass hc A hA = ∑ i, resSetClass hc (D i) (hD i) := by
  have he : A.carrier = (rvFiniteUnion Finset.univ D).carrier := by
    ext r
    rw [rvFiniteUnion_mem, hcovers]
    simp
  exact (resSetClass_congr hc A _ hA _ he).trans
    (resSetClass_finiteUnion hc Finset.univ D hD (fun _ _ _ _ h => hd h))

end DiamondIntegral.Section5
