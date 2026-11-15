import «section 5».DiagonalConstructibleRing

/-! Finite invariant constructible partitions give literal additive
decompositions in the raw diagonal ring. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
open Classical FirstOrder FirstOrder.Language
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def ofSet {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X) : Object :=
  ⟨n, q, X, hX, hiX⟩

def setClass {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X) : Ring :=
  objectClass (ofSet q X hX hiX)

theorem setClass_congr {n : ℕ} (q : Fin n → ℚ) (X Y : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X)
    (hY : (Set.univ : Set ℂ).Definable Language.ring Y) (hiY : RationalInvariant q Y)
    (he : X = Y) : setClass q X hX hiX = setClass q Y hY hiY := by
  subst Y
  rfl

theorem rationalInvariant_union {n : ℕ} (q : Fin n → ℚ) (X Y : Set (Fin n → ℂ))
    (hX : RationalInvariant q X) (hY : RationalInvariant q Y) : RationalInvariant q (X ∪ Y) :=
  fun η x => or_congr (hX η x) (hY η x)

theorem setClass_disjoint_union {n : ℕ} (q : Fin n → ℚ) (X Y : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X)
    (hY : (Set.univ : Set ℂ).Definable Language.ring Y) (hiY : RationalInvariant q Y)
    (hd : Disjoint X Y) :
    setClass q (X ∪ Y) (hX.union hY) (rationalInvariant_union q X Y hiX hiY) =
      setClass q X hX hiX + setClass q Y hY hiY := by
  let U := ofSet q (X ∪ Y) (hX.union hY) (rationalInvariant_union q X Y hiX hiY)
  have h := objectClass_scissor U X hX hiX
  have heI : (X ∪ Y) ∩ X = X := by ext x; simp only [Set.mem_inter_iff, Set.mem_union]; tauto
  have heO : (X ∪ Y) \ X = Y := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      exact hx.resolve_left hn
    · intro hx
      exact ⟨Or.inr hx, fun hy => Set.disjoint_left.mp hd hy hx⟩
  have hi : objectClass (cut U X hX hiX) = setClass q X hX hiX :=
    setClass_congr q _ X _ _ hX hiX heI
  have ho : objectClass (outside U X hX hiX) = setClass q Y hY hiY :=
    setClass_congr q _ Y _ _ hY hiY heO
  exact h.trans (congrArg₂ (· + ·) hi ho)

theorem finsetSup_mem {n : ℕ} {I : Type} (s : Finset I) (D : I → Set (Fin n → ℂ)) (x : Fin n → ℂ) :
    x ∈ s.sup D ↔ ∃ i ∈ s, x ∈ D i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert, Set.sup_eq_union, Set.mem_union, ih, Finset.mem_insert]
    constructor
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact ⟨i, Or.inl rfl, hx⟩
      · exact ⟨j, Or.inr hj, hx⟩
    · rintro ⟨j, hj | hj, hx⟩
      · subst j
        exact Or.inl hx
      · exact Or.inr ⟨j, hj, hx⟩

theorem finsetSup_invariant {n : ℕ} {I : Type} (q : Fin n → ℚ) (s : Finset I)
    (D : I → Set (Fin n → ℂ)) (hD : ∀ i, RationalInvariant q (D i)) : RationalInvariant q (s.sup D) := by
  intro η x
  rw [finsetSup_mem, finsetSup_mem]
  exact exists_congr (fun i => and_congr Iff.rfl (hD i η x))

def finiteUnion {n : ℕ} {I : Type} (q : Fin n → ℚ) (s : Finset I)
    (D : I → Set (Fin n → ℂ))
    (hD : ∀ i, (Set.univ : Set ℂ).Definable Language.ring (D i))
    (hiD : ∀ i, RationalInvariant q (D i)) : Object :=
  ofSet q (s.sup D) (Set.definable_finset_sup hD s) (finsetSup_invariant q s D hiD)

theorem finiteUnion_class {n : ℕ} {I : Type} (q : Fin n → ℚ) (s : Finset I)
    (D : I → Set (Fin n → ℂ))
    (hD : ∀ i, (Set.univ : Set ℂ).Definable Language.ring (D i))
    (hiD : ∀ i, RationalInvariant q (D i))
    (hd : Set.PairwiseDisjoint (s : Set I) D) :
    objectClass (finiteUnion q s D hD hiD) = ∑ i ∈ s, setClass q (D i) (hD i) (hiD i) := by
  induction s using Finset.induction_on with
  | empty => exact objectClass_empty _ rfl
  | @insert i s hi ih =>
    have hdis : Disjoint (D i) (s.sup D) := by
      apply Set.disjoint_left.mpr
      intro x hx hs
      obtain ⟨j, hj, hxj⟩ := (finsetSup_mem s D x).mp hs
      exact Set.disjoint_left.mp (hd (by simp) (by simp [hj]) (by intro he; exact hi (he ▸ hj))) hx hxj
    have hrest : Set.PairwiseDisjoint (s : Set I) D :=
      fun j hj k hk hjk => hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
    have hunion := setClass_disjoint_union q (D i) (s.sup D) (hD i) (hiD i)
      (Set.definable_finset_sup hD s) (finsetSup_invariant q s D hiD) hdis
    have he : objectClass (finiteUnion q (insert i s) D hD hiD) =
        setClass q (D i) (hD i) (hiD i) + objectClass (finiteUnion q s D hD hiD) := by
      exact (setClass_congr q _ _ _ _ _ _ (Finset.sup_insert (f := D))).trans hunion
    rw [he, ih hrest, Finset.sum_insert hi]

theorem finite_partition_class {n : ℕ} {I : Type} [Fintype I] (q : Fin n → ℚ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hiX : RationalInvariant q X) (D : I → Set (Fin n → ℂ))
    (hD : ∀ i, (Set.univ : Set ℂ).Definable Language.ring (D i))
    (hiD : ∀ i, RationalInvariant q (D i)) (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hc : ∀ x, x ∈ X ↔ ∃ i, x ∈ D i) :
    setClass q X hX hiX = ∑ i, setClass q (D i) (hD i) (hiD i) := by
  have he : X = Finset.univ.sup D := by
    ext x
    rw [hc, finsetSup_mem]
    simp
  exact (setClass_congr q X _ hX hiX _ _ he).trans
    (finiteUnion_class q Finset.univ D hD hiD (fun _ _ _ _ h => hd h))

end DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
