import Section3.DefinableLocalChoice

/-!
# Same-base finite-valued choice from algebraic points

The checked scalar good-relation construction supplies finite rows.
Taking products gives tuple rows; genuine saturation gives a finite
subcover of their domains. Their union is still finite-valued. No single
algebraic conjugate is chosen as a definable function.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
namespace FiniteChoice
variable {M : Type} [LRV.Structure M] {n m : ℕ}

def RelationDefinable (S : Set M) (R : Set ((Fin n → M) × (Fin m → M))) : Prop :=
  S.Definable LRV {z : Fin n ⊕ Fin m → M | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}

def GoodRelation (S : Set M) (P : Set ((Fin n → M) × (Fin m → M))) :=
  {R : Set ((Fin n → M) × (Fin m → M)) // RelationDefinable S R ∧
    (∀ x : Fin n → M, {y | (x,y) ∈ R}.Finite) ∧ R ⊆ P}

theorem good_relation_of_algebraic (S : Set M) (P : Set ((Fin n → M) × (Fin m → M)))
    (hP : RelationDefinable S P) (a : Fin n → M) (b : Fin m → M) (hab : (a,b) ∈ P)
    (hb : ∀ i, RawClosure.AlgebraicOver (S ∪ Set.range a) (b i)) :
    ∃ R : GoodRelation S P, (a,b) ∈ R.val := by
  classical
  choose R hR using fun i => RawClosure.Tuple.good_relation_of_algebraic S a (b i) (hb i)
  let U : Set ((Fin n → M) × (Fin m → M)) :=
    {p | (∀ i, (p.1, p.2 i) ∈ (R i).val) ∧ p ∈ P}
  have hc (i : Fin m) : S.Definable LRV
      {z : Fin n ⊕ Fin m → M | (z ∘ Sum.inl, z (.inr i)) ∈ (R i).val} := by
    exact (R i).property.1.preimage_comp
      (Sum.elim Sum.inl (fun _ : Fin 1 => Sum.inr i))
  have hU : RelationDefinable S U := by
    change S.Definable LRV {z : Fin n ⊕ Fin m → M | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ U}
    convert (Set.definable_iInter_of_finite hc).inter hP using 1
    ext z
    simp only [U, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Function.comp_apply]
  refine ⟨⟨U, hU, ?_, fun _ hp => hp.2⟩, fun i => hR i, hab⟩
  intro x
  exact (Set.Finite.pi' (fun i => (R i).property.2 x)).subset (fun _ hy => hy.1)

theorem domain_definable (S : Set M) (R : Set ((Fin n → M) × (Fin m → M)))
    (hR : RelationDefinable S R) : S.Definable LRV {x | ∃ y, (x,y) ∈ R} := by
  exact hR.exists_of_finite

/-- The admissible relation is defined over S; only the domain cover may
use additional small parameters T. The resulting finite-valued relation
still uses S alone. -/
theorem definable_finite_choice_over {κ : Cardinal} (hs : Saturated M κ)
    (S T : Set M) (hST : S ⊆ T) (hsmall : Cardinal.mk T < κ)
    (A : Set (Fin n → M)) (hA : T.Definable LRV A)
    (P : Set ((Fin n → M) × (Fin m → M))) (hP : RelationDefinable S P)
    (hlocal : ∀ a ∈ A, ∃ b, (a,b) ∈ P ∧
      ∀ i, RawClosure.AlgebraicOver (S ∪ Set.range a) (b i)) :
    ∃ R : GoodRelation S P, ∀ a ∈ A, ∃ b, (a,b) ∈ R.val := by
  classical
  let dom (R : GoodRelation S P) : Set (Fin n → M) := {a | ∃ b, (a,b) ∈ R.val}
  let C := Set.range dom
  have hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨b, hab, hb⟩ := hlocal a ha
    obtain ⟨R, haR⟩ := good_relation_of_algebraic S P hP a b hab hb
    exact ⟨dom R, Set.mem_range_self R, b, haR⟩
  obtain ⟨C₀, hfin, hsub, hcov⟩ := hs.definable_finite_subcover_tuple T hsmall A hA C
    (by rintro c ⟨R,rfl⟩; exact (domain_definable S R.val R.property.1).mono hST) hcover
  haveI : Finite C₀ := hfin.to_subtype
  let rel (c : C₀) : GoodRelation S P := Classical.choose (hsub c.property)
  have hrel (c : C₀) : dom (rel c) = c.val := Classical.choose_spec (hsub c.property)
  let U : Set ((Fin n → M) × (Fin m → M)) := {p | ∃ c : C₀, p ∈ (rel c).val}
  have hU : RelationDefinable S U := by
    have h := Set.definable_iUnion_of_finite (fun c : C₀ => (rel c).property.1)
    simpa only [RelationDefinable, U, Set.mem_ofPred_eq, Set.iUnion_ofPred] using h
  have hf (a : Fin n → M) : {b | (a,b) ∈ U}.Finite := by
    have h := Set.finite_iUnion (fun c : C₀ => (rel c).property.2.1 a)
    simpa only [U, Set.mem_ofPred_eq, Set.iUnion_ofPred] using h
  refine ⟨⟨U, hU, hf, ?_⟩, ?_⟩
  · rintro p ⟨c, hp⟩
    exact (rel c).property.2.2 hp
  · intro a ha
    obtain ⟨c, hc, hac⟩ := hcov a ha
    have h : a ∈ dom (rel ⟨c,hc⟩) := by rwa [hrel]
    obtain ⟨b, hb⟩ := h
    exact ⟨b, ⟨c,hc⟩, hb⟩

/-- A complete same-base graph of finite sets, nonempty exactly on A,
contained in the prescribed relation. Tuple arities may be zero. -/
theorem definable_finite_choice {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (P : Set ((Fin n → M) × (Fin m → M))) (hP : RelationDefinable S P)
    (hlocal : ∀ a ∈ A, ∃ b, (a,b) ∈ P ∧
      ∀ i, RawClosure.AlgebraicOver (S ∪ Set.range a) (b i)) :
    ∃ F : (Fin n → M) → Set (Fin m → M),
      RelationDefinable S {p | p.2 ∈ F p.1} ∧
      (∀ a, (F a).Finite) ∧
      (∀ a b, b ∈ F a → (a,b) ∈ P) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  obtain ⟨R, hR⟩ := definable_finite_choice_over hs S S (Set.Subset.refl _) hsmall A hA P hP hlocal
  let F (a : Fin n → M) : Set (Fin m → M) := {b | a ∈ A ∧ (a,b) ∈ R.val}
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact (hA.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin m)).inter R.property.1
  · intro a
    exact (R.property.2.1 a).subset (fun _ hb => hb.2)
  · exact fun _ _ hb => R.property.2.2 hb.2
  · intro a
    exact ⟨fun ⟨_,hb⟩ => hb.1, fun ha => by
      obtain ⟨b,hb⟩ := hR a ha
      exact ⟨b,ha,hb⟩⟩

end FiniteChoice
end DiamondIntegral.Section2
