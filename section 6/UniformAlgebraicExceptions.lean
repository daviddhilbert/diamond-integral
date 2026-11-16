import «section 6».FiniteMeasuredVFChainLifting
import Section3.TupleRelations
import Section3.TupleCompactness

/-! A uniform finite-exception construction. If every inverse row is
finite or its distinguished label is algebraic over the original
parameters, compactness gives one original-base finite-fibre exceptional
relation and a single bound on every complementary row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M} {n : ℕ}

def finiteRelationGraph (Q : RawClosure.Tuple.GoodRelation (n := n) S) : Set (Fin (n+1) → M) :=
  {p | (Fin.init p,p (Fin.last n)) ∈ Q.val}

theorem finiteRelationGraph_definable (Q : RawClosure.Tuple.GoodRelation (n := n) S) :
    S.Definable LRV (finiteRelationGraph Q) :=
  Q.property.1.preimage_comp (Sum.elim Fin.castSucc (fun _ : Fin 1 => Fin.last n))

def emptyFiniteRelation (S : Set M) (n : ℕ) : RawClosure.Tuple.GoodRelation (n := n) S :=
  ⟨∅,by
    change S.Definable LRV (∅ : Set (Fin n ⊕ Fin 1 → M))
    exact Set.definable_empty,
    fun _ => Set.finite_empty⟩

theorem uniform_algebraic_exceptions {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (R : Set ((Fin (n+1) → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (hEither : ∀ p : Fin (n+1) → M,
      {x | (p,x) ∈ R}.Finite ∨
        RawClosure.AlgebraicOver (S ∪ Set.range (Fin.init p)) (p (Fin.last n))) :
    ∃ E : RawClosure.Tuple.GoodRelation (n := n) S, ∃ N : ℕ,
      ∀ p : Fin (n+1) → M, (Fin.init p,p (Fin.last n)) ∉ E.val →
        {x | (p,x) ∈ R}.Finite ∧ {x | (p,x) ∈ R}.ncard ≤ N := by
  let I := ℕ ⊕ RawClosure.Tuple.GoodRelation (n := n) S
  let D (i : I) : Set (Fin (n+1) → M) := match i with
    | .inl k => (RawClosure.Tuple.HasMore R k)ᶜ
    | .inr Q => finiteRelationGraph Q
  have hD (i : I) : S.Definable LRV (D i) := by
    cases i with
    | inl k => exact (RawClosure.Tuple.hasMore_definable S R hR k).compl
    | inr Q => exact finiteRelationGraph_definable Q
  have hcover (p : Fin (n+1) → M) (hp : p ∈ Set.univ) : ∃ d ∈ Set.range D, p ∈ d := by
    rcases hEither p with hf | ha
    · refine ⟨D (.inl {x | (p,x) ∈ R}.ncard),⟨.inl _,rfl⟩,?_⟩
      exact RawClosure.no_inj_iff_finite_ncard_le.mpr ⟨hf,le_rfl⟩
    · obtain ⟨Q,hQ⟩ := RawClosure.Tuple.good_relation_of_algebraic S (Fin.init p) (p (Fin.last n)) ha
      exact ⟨D (.inr Q),⟨.inr Q,rfl⟩,hQ⟩
  obtain ⟨C,hC,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall Set.univ
    (Set.definable_univ (A := S) (L := LRV)) (Set.range D) (by rintro _ ⟨i,rfl⟩; exact hD i) hcover
  letI : Fintype C := hC.fintype
  have hindex (c : C) : ∃ i : I, D i = c.val := hSub c.property
  let idx (c : C) : I := Classical.choose (hindex c)
  have hidx (c : C) : D (idx c) = c.val := Classical.choose_spec (hindex c)
  let term (c : C) : ℕ := match idx c with | .inl k => k | .inr _ => 0
  let Q (c : C) : RawClosure.Tuple.GoodRelation (n := n) S :=
    match idx c with | .inl _ => emptyFiniteRelation S n | .inr Q => Q
  let E : Set ((Fin n → M) × M) := ⋃ c : C, (Q c).val
  have hE : RawClosure.Tuple.RelationDefinable S E := by
    have h := Set.definable_iUnion_of_finite (fun c : C => (Q c).property.1)
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ E}
    convert h using 1
    ext z
    simp only [RawClosure.Tuple.RelationDefinable,E,Set.mem_iUnion,Set.mem_setOf_eq]
  have hEF (a : Fin n → M) : {b | (a,b) ∈ E}.Finite := by
    convert Set.finite_iUnion (fun c : C => (Q c).property.2 a) using 1
    ext b
    simp only [E,Set.mem_iUnion,Set.mem_setOf_eq]
  refine ⟨⟨E,hE,hEF⟩,∑ c : C, term c,fun p hp => ?_⟩
  obtain ⟨d,hd,hpd⟩ := hCov p (Set.mem_univ _)
  let c : C := ⟨d,hd⟩
  have hpc : p ∈ D (idx c) := by rw [hidx]; exact hpd
  cases he : idx c with
  | inl k =>
    have hb : p ∉ RawClosure.Tuple.HasMore R k := by simpa only [D,he,Set.mem_compl_iff] using hpc
    have hf := (RawClosure.no_inj_iff_finite_ncard_le (s := {x | (p,x) ∈ R}) (k := k)).mp hb
    refine ⟨hf.1,hf.2.trans ?_⟩
    have h := Finset.single_le_sum (fun c _ => Nat.zero_le (term c)) (Finset.mem_univ c)
    simpa only [term,he] using h
  | inr q =>
    have hq : (Fin.init p,p (Fin.last n)) ∈ q.val := by simpa only [D,he,finiteRelationGraph,Set.mem_setOf_eq] using hpc
    apply False.elim
    apply hp
    apply Set.mem_iUnion.mpr
    refine ⟨c,?_⟩
    change (Fin.init p,p (Fin.last n)) ∈ (Q c).val
    simpa only [Q,he] using hq

end DiamondIntegral.Section6
