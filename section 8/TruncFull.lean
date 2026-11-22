import «section 8».TruncLemma85
import «section 8».TruncAmbient
import FubiniTheorems.Comparison.RESFinitePartitions
import FubiniTheorems.Comparison.RESSetOperations

/-! The full truncation set and its class.

For a concrete set `X` definable over `ℂ((t))` (mixed sorts `n`, `l`), cutoffs `β = b/m` and a finite
set `Q` of label patterns covering the labels of the `m`-rational integral points:

* `fullTruncSet m b A`: the truncation `A[m;β]` (all labels) as a set of RV tuples of the concrete
  model, coordinates enumerated by `εt`;
* `fullTruncSet_definable`: it is definable over `ℂ((t))` (a finite union of the definable pieces of
  `truncation_definable`);
* `fullTruncSet_finite_values`: its value tuples form a finite set;
* `fullClass`: `Θ([A[m;β]]) [𝔸]^{-mΣβ} ∈ K^μ̂ Var_ℂ[[𝔸]⁻¹]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm

local instance fullTruncStructure : LRV.Structure Carrier := canonicalInterpret
local instance fullTruncModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {n l : ℕ} (m : ℕ+) (b : Fin n → ℕ)

/-- The number of truncation coordinates. -/
abbrev Kt (b : Fin n → ℕ) (l : ℕ) : ℕ := Fintype.card (Idx b ⊕ Fin l)

/-- The enumeration of the truncation coordinates. -/
abbrev εt (b : Fin n → ℕ) (l : ℕ) : Idx b ⊕ Fin l ≃ Fin (Kt b l) := Fintype.equivFin _

/-- **The full truncation set** as RV tuples. -/
def fullTruncSet (A : Set ((Fin n → Ser) × (Fin l → RV))) : Set (Fin (Kt b l) → CanonicalRV.RVSort Carrier) :=
  {r | (fun a => taggedRVEquiv (r (εt b l a))) ∈ truncSet m b A}

/-- The label patterns `Q` cover the labels of the rational integral points of `A`. -/
def Covers (Q : Finset (Fin l → ℤ)) (A : Set ((Fin n → Ser) × (Fin l → RV))) : Prop :=
  ∀ p ∈ A, (∀ i, IsRational m (p.1 i) ∧ IsIntegral (p.1 i)) → (∀ j, LabelRational m (p.2 j)) →
    ∃ q ∈ Q, ∀ j, p.2 j ∈ Line (zlev m (q j))

theorem truncSet_label {A : Set ((Fin n → Ser) × (Fin l → RV))} {Q : Finset (Fin l → ℤ)}
    (hQ : Covers m Q A) {w : Idx b ⊕ Fin l → RV} (hw : w ∈ truncSet m b A) :
    ∃ q ∈ Q, ∀ j, w (.inr j) ∈ Line (zlev m (q j)) := by
  obtain ⟨p, hp, hr, hu, rfl⟩ := hw
  exact hQ p hp hr hu

variable {X : Set (Fin (n + l) → Carrier)}

/-- The descended set of one label pattern. -/
def patternSet (q : Fin l → ℤ) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) :
    DefSet (rawRVSpace (M := Carrier) (Kt b l)) {c | baseCarrier c} :=
  rationalDescendedSet (truncObject m b q hX (εt b l)).weights (truncObject m b q hX (εt b l)).domain
    (truncObject m b q hX (εt b l)).definable

theorem mem_patternSet (q : Fin l → ℤ) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (r : Fin (Kt b l) → CanonicalRV.RVSort Carrier) :
    r ∈ (patternSet m b q hX).carrier ↔
      (fun a => taggedRVEquiv (r (εt b l a))) ∈
        {w | w ∈ truncSet m b (mixedSet X) ∧ ∀ j, w (.inr j) ∈ Line (zlev m (q j))} := by
  have hdef : (Set.univ : Set ℂ).Definable Language.ring
      {x : Fin (Kt b l) → ℂ | x ∘ εt b l ∈ coeffSet m b q (mixedSet X)} := by
    rw [coeffSet_eq]
    exact (truncObject m b q hX (εt b l)).definable
  have hinv : RationalInvariant (stdWt m b q ∘ (εt b l).symm)
      {x : Fin (Kt b l) → ℂ | x ∘ εt b l ∈ coeffSet m b q (mixedSet X)} := by
    rw [coeffSet_eq]
    exact (truncObject m b q hX (εt b l)).invariant
  have hdom : (truncObject m b q hX (εt b l)).domain = {x | x ∘ εt b l ∈ coeffSet m b q (mixedSet X)} :=
    truncObject_domain m b q hX (εt b l)
  have hw : (truncObject m b q hX (εt b l)).weights = stdWt m b q ∘ (εt b l).symm := rfl
  change r ∈ (rationalDescendedSet _ _ _).carrier ↔ _
  rw [rationalDescent_mem_image _ _ _ (truncObject m b q hX (εt b l)).invariant, hdom, hw,
    truncSet_pattern_eq m b q _ hA]
  have hframe : ∀ x : Fin (Kt b l) → ℂ,
      (fun a => taggedRVEquiv (rationalFrame (stdWt m b q ∘ (εt b l).symm) x (εt b l a))) =
        frameOf m b q (x ∘ εt b l) := by
    intro x
    funext a
    cases a with
    | inl k =>
      show linePoint (stdWt m b q ((εt b l).symm (εt b l (Sum.inl k)))) (x (εt b l (Sum.inl k))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    | inr j =>
      show linePoint (stdWt m b q ((εt b l).symm (εt b l (Sum.inr j)))) (x (εt b l (Sum.inr j))) = _
      rw [Equiv.symm_apply_apply]
      rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hframe]
    exact ⟨x ∘ εt b l, hx, rfl⟩
  · rintro ⟨c, hc, he⟩
    have hcomp : (c ∘ (εt b l).symm) ∘ εt b l = c := by funext a; simp
    refine ⟨c ∘ (εt b l).symm, ?_, ?_⟩
    · show (c ∘ (εt b l).symm) ∘ εt b l ∈ coeffSet m b q (mixedSet X)
      rw [hcomp]
      exact hc
    · have h1 := hframe (c ∘ (εt b l).symm)
      rw [hcomp, he] at h1
      funext i
      have h2 := congrFun h1 ((εt b l).symm i)
      simp only [Equiv.apply_symm_apply] at h2
      exact taggedRVEquiv.injective h2

theorem fullTruncSet_eq_iUnion (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    fullTruncSet m b (mixedSet X) = ⋃ q ∈ Q, (patternSet m b q hX).carrier := by
  ext r
  simp only [Set.mem_iUnion, mem_patternSet m b _ hX hA, exists_prop]
  constructor
  · intro hr
    obtain ⟨q, hq, hl⟩ := truncSet_label m b hQ hr
    exact ⟨q, hq, hr, hl⟩
  · rintro ⟨q, -, hr, -⟩
    exact hr

theorem fullTruncSet_definable (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    (rawRVSpace (M := Carrier) (Kt b l)).Definable {c | baseCarrier c} (fullTruncSet m b (mixedSet X)) := by
  rw [fullTruncSet_eq_iUnion m b Q hX hA hQ]
  change {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) (Kt b l)).preimage _)
  have h : ∀ q, {c | baseCarrier c}.Definable LRV
      ((rawRVSpace (M := Carrier) (Kt b l)).preimage (patternSet m b q hX).carrier) :=
    fun q => (patternSet m b q hX).definable
  have he : (rawRVSpace (M := Carrier) (Kt b l)).preimage (⋃ q ∈ Q, (patternSet m b q hX).carrier) =
      ⋃ q ∈ Q, (rawRVSpace (M := Carrier) (Kt b l)).preimage (patternSet m b q hX).carrier := by
    ext z
    simp only [Space.preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨hz, q, hq, hm⟩
      exact ⟨q, hq, hz, hm⟩
    · rintro ⟨q, hq, hz, hm⟩
      exact ⟨hz, q, hq, hm⟩
  rw [he]
  exact Set.definable_biUnion_finset h Q

/-- **The full truncation set** as a definable set. -/
def fullTruncDefSet (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    DefSet (rawRVSpace (M := Carrier) (Kt b l)) {c | baseCarrier c} :=
  ⟨fullTruncSet m b (mixedSet X), fullTruncSet_definable m b Q hX hA hQ⟩

/-! ### Values -/

theorem iLe_rvTag (r s : RV) : iLe (rvTag r).val (rvTag s).val ↔ value r ≤ value s := by
  change ((∀ i : Fin 2, ¬ inVF ((![Sum.inr r, Sum.inr s] : Fin 2 → Carrier) i)) ∧
      ¬ inVF (Sum.inr r : Carrier) ∧ ¬ inVF (Sum.inr s : Carrier) ∧
      value (rvPart (Sum.inr r)) ≤ value (rvPart (Sum.inr s))) ↔ _
  simp only [inVF, not_false_eq_true, and_true, true_and]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨fun i => by fin_cases i <;> exact not_false, h⟩

/-- The value of an RV element of the concrete model, in the abstract value set. -/
def vrvOf (v : WithTop ℚ) : Values.GammaTop (M := Carrier) :=
  match v with
  | ⊤ => Values.vrv (rvTag none)
  | (q : ℚ) => Values.vrv (rvTag (some (Multiplicative.ofAdd q, 1)))

theorem vrv_rvTag (r : RV) : Values.vrv (rvTag r) = vrvOf (value r) := by
  cases r with
  | none => rfl
  | some u =>
    change Values.vrv (rvTag (some u)) = Values.vrv (rvTag (some (Multiplicative.ofAdd u.1.toAdd, 1)))
    rw [Values.vrv_eq_iff]
    refine ⟨(iLe_rvTag _ _).mpr ?_, (iLe_rvTag _ _).mpr ?_⟩ <;> simp [value]

/-- The finite set of values of the truncation coordinates. -/
def valueSet (Q : Finset (Fin l → ℤ)) : Finset (WithTop ℚ) :=
  insert ⊤ ((Finset.range ((Finset.univ.sup b) + 1)).image (fun k => ((lev m k : ℚ) : WithTop ℚ)) ∪
    (Q ×ˢ Finset.univ).image (fun qj : (Fin l → ℤ) × Fin l => ((zlev m (qj.1 qj.2) : ℚ) : WithTop ℚ)))

theorem value_coeffRV (γ : ℚ) (c : ℂ) : value (coeffRV γ c) = ⊤ ∨ value (coeffRV γ c) = γ := by
  unfold coeffRV
  split_ifs
  · left; rfl
  · right; rfl

theorem value_line {γ : ℚ} {r : RV} (hr : r ∈ Line γ) : value r = ⊤ ∨ value r = γ := by
  rcases hr with rfl | ⟨c, rfl⟩
  · left; rfl
  · right; rfl

theorem fullTruncSet_values (Q : Finset (Fin l → ℤ)) (A : Set ((Fin n → Ser) × (Fin l → RV)))
    (hQ : Covers m Q A) {r : Fin (Kt b l) → CanonicalRV.RVSort Carrier} (hr : r ∈ fullTruncSet m b A)
    (i : Fin (Kt b l)) : value (taggedRVEquiv (r i)) ∈ valueSet m b Q := by
  obtain ⟨q, hq, hl⟩ := truncSet_label m b hQ hr
  have hi : i = εt b l ((εt b l).symm i) := ((εt b l).apply_symm_apply i).symm
  rw [hi]
  rcases hc : (εt b l).symm i with k | j
  · obtain ⟨p, -, -, -, hw⟩ := hr
    have hk := congrFun hw (.inl k)
    simp only [Sum.elim_inl] at hk
    rw [hk]
    rcases value_coeffRV (lev m k.2) (cf (p.1 k.1) (lev m k.2)) with h | h
    · rw [truncPoint, h]; exact Finset.mem_insert_self _ _
    · rw [truncPoint, h]
      refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k.2, ?_, rfl⟩))
      rw [Finset.mem_range]
      have h1 : (k.2 : ℕ) ≤ b k.1 := Nat.lt_succ_iff.mp k.2.isLt
      have h2 : b k.1 ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ _)
      omega
  · rcases value_line (hl j) with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(q, j), Finset.mem_product.mpr ⟨hq, Finset.mem_univ _⟩, rfl⟩))

theorem fullTruncSet_finite_values (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    (Set.range (fun u : fullTruncDefSet m b Q hX hA hQ => fun i => Values.vrv (u.val i))).Finite := by
  have hfin : (Set.pi Set.univ (fun _ : Fin (Kt b l) => ((valueSet m b Q : Set (WithTop ℚ))))).Finite :=
    Set.Finite.pi (fun _ => (valueSet m b Q).finite_toSet)
  apply (hfin.image (fun v i => vrvOf (v i))).subset
  rintro _ ⟨u, rfl⟩
  refine ⟨fun i => value (taggedRVEquiv (u.val i)), fun i _ => fullTruncSet_values m b Q _ hQ u.property i, ?_⟩
  funext i
  have h := vrv_rvTag (taggedRVEquiv (u.val i))
  rw [show rvTag (taggedRVEquiv (u.val i)) = u.val i from taggedRVEquiv.symm_apply_apply _] at h
  exact h.symm

/-- **The normalized class of the truncation** `Θ([A[m;β]]) [𝔸]^{-mΣβ}`. -/
def fullClass (Q : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) : Rloc :=
  algebraMap EquivariantVariety.ModifiedRing Rloc
      (theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
        (resSetClass canonicalInterpret_isCanonical (fullTruncDefSet m b Q hX hA hQ)
          (fullTruncSet_finite_values m b Q hX hA hQ)))) * Linv (∑ i, b i)

/-! ### The class as a sum over label patterns -/

/-- The labels of the points of `A` are nonzero. -/
def LabelsNonzero (A : Set ((Fin n → Ser) × (Fin l → RV))) : Prop := ∀ p ∈ A, ∀ j, p.2 j ≠ none

theorem line_disjoint {γ δ : ℚ} (h : γ ≠ δ) {r : RV} (hr : r ≠ none) (h1 : r ∈ Line γ) (h2 : r ∈ Line δ) :
    False := by
  rcases h1 with h1 | ⟨c, rfl⟩
  · exact hr h1
  · rcases h2 with h2 | ⟨c', h2⟩
    · exact hr h2
    · have := congrArg (fun u : RV => u.map (fun v => v.1)) h2
      simp only [Option.map_some] at this
      exact h (Multiplicative.ofAdd.injective (Option.some_injective _ this))

theorem patternSet_class (q : Fin l → ℤ) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) :
    theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
      (resSetClass canonicalInterpret_isCanonical (patternSet m b q hX)
        (rationalDescendedSet_finite_values _ _ _))) =
      dcClass (truncObject m b q hX (εt b l)) :=
  theta_diagonalRESClass _

/-- The union of the pattern sets of a finite set of patterns. -/
def unionDefSet (Q₀ : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) :
    DefSet (rawRVSpace (M := Carrier) (Kt b l)) {c | baseCarrier c} := by
  refine ⟨⋃ q ∈ Q₀, (patternSet m b q hX).carrier, ?_⟩
  change {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) (Kt b l)).preimage _)
  have he : (rawRVSpace (M := Carrier) (Kt b l)).preimage (⋃ q ∈ Q₀, (patternSet m b q hX).carrier) =
      ⋃ q ∈ Q₀, (rawRVSpace (M := Carrier) (Kt b l)).preimage (patternSet m b q hX).carrier := by
    ext z
    simp only [Space.preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨hz, q, hq, hm⟩
      exact ⟨q, hq, hz, hm⟩
    · rintro ⟨q, hq, hz, hm⟩
      exact ⟨hz, q, hq, hm⟩
  rw [he]
  exact Set.definable_biUnion_finset (fun q => (patternSet m b q hX).definable) Q₀

theorem unionDefSet_finite (Q₀ : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) :
    (Set.range (fun u : unionDefSet m b Q₀ hX => fun i => Values.vrv (u.val i))).Finite := by
  have hfin : (⋃ q ∈ Q₀, Set.range (fun u : patternSet m b q hX => fun i => Values.vrv (u.val i))).Finite :=
    Set.Finite.biUnion Q₀.finite_toSet (fun q _ => rationalDescendedSet_finite_values _ _ _)
  apply hfin.subset
  rintro _ ⟨u, rfl⟩
  obtain ⟨q, hq, hu⟩ := Set.mem_iUnion₂.mp u.property
  exact Set.mem_iUnion₂.mpr ⟨q, hq, ⟨⟨u.val, hu⟩, rfl⟩⟩

theorem resSetClass_union_eq_sum (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hnz : LabelsNonzero (mixedSet X)) (Q₀ : Finset (Fin l → ℤ)) :
    resSetClass canonicalInterpret_isCanonical (unionDefSet m b Q₀ hX) (unionDefSet_finite m b Q₀ hX) =
      ∑ q ∈ Q₀, resSetClass canonicalInterpret_isCanonical (patternSet m b q hX)
        (rationalDescendedSet_finite_values _ _ _) := by
  induction Q₀ using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    apply resSetClass_empty
    simp [unionDefSet]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    apply resSetClass_disjoint_union
    · rw [Set.disjoint_left]
      intro r hra hrs
      obtain ⟨q, hq, hrq⟩ := Set.mem_iUnion₂.mp hrs
      have hqa : q ≠ a := fun h => ha (h ▸ hq)
      obtain ⟨j, hj⟩ : ∃ j, q j ≠ a j := by
        by_contra hall
        push Not at hall
        exact hqa (funext hall)
      have h1 := (mem_patternSet m b a hX hA r).mp hra
      have h2 := (mem_patternSet m b q hX hA r).mp hrq
      obtain ⟨p, hp, -, -, hw⟩ := h1.1
      have hlab : taggedRVEquiv (r (εt b l (.inr j))) = p.2 j := congrFun hw (.inr j)
      apply line_disjoint (γ := zlev m (a j)) (δ := zlev m (q j))
        (fun h => hj (zlev_injective m h).symm) (r := taggedRVEquiv (r (εt b l (.inr j))))
      · rw [hlab]; exact hnz p hp j
      · exact h1.2 j
      · exact h2.2 j
    · ext r
      simp [unionDefSet, patternSet]

theorem fullTruncDefSet_eq_union (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    fullTruncDefSet m b Q hX hA hQ = unionDefSet m b Q hX := by
  cases h : fullTruncDefSet m b Q hX hA hQ with
  | mk c hc =>
    have hcar : c = (unionDefSet m b Q hX).carrier := by
      have := congrArg DefSet.carrier h
      simp only [fullTruncDefSet] at this
      rw [← this]
      exact fullTruncSet_eq_iUnion m b Q hX hA hQ
    subst hcar
    rfl

/-- **The class is the sum of the pattern classes.** -/
theorem fullClass_eq_sum (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) (hnz : LabelsNonzero (mixedSet X)) :
    fullClass m b Q hX hA hQ = ∑ q ∈ Q, truncClass m b q hX := by
  have h1 : resSetClass canonicalInterpret_isCanonical (fullTruncDefSet m b Q hX hA hQ)
      (fullTruncSet_finite_values m b Q hX hA hQ) =
      resSetClass canonicalInterpret_isCanonical (unionDefSet m b Q hX) (unionDefSet_finite m b Q hX) := by
    congr 1
    exact fullTruncDefSet_eq_union m b Q hX hA hQ
  rw [fullClass, h1, resSetClass_union_eq_sum m b hX hA hnz Q, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [truncClass, patternSet_class]

theorem invariant_mono {b b' : Fin n → ℕ} (h : ∀ i, b i ≤ b' i) {A : Set ((Fin n → Ser) × (Fin l → RV))}
    (hA : Invariant m b A) : Invariant m b' A := by
  intro x x' u hx hc
  refine hA x x' u hx fun i γ hγ => hc i γ (le_trans hγ ?_)
  rcases Nat.lt_or_eq_of_le (h i) with hlt | heq
  · exact (lev_lt_lev hlt).le
  · rw [heq]

/-- **Lemma 8.5 for the class of the full truncation**: it does not depend on the cutoffs. -/
theorem fullClass_cutoff {b b' : Fin n → ℕ} (h : ∀ i, b i ≤ b' i) (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) (hnz : LabelsNonzero (mixedSet X)) :
    fullClass m b' Q hX (invariant_mono m h hA) hQ = fullClass m b Q hX hA hQ := by
  rw [fullClass_eq_sum m b' Q hX _ hQ hnz, fullClass_eq_sum m b Q hX hA hQ hnz]
  exact Finset.sum_congr rfl fun q _ => lemma_8_5 m h q hX hA

end DiamondIntegral.Section8.Truncation
