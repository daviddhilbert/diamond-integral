import «section 6».DiamondGroupoid
import «section 6».ClopenCriterion
import «section 6».UnaryRootControl
import ValuedFieldExtension

/-! (Moved from `section 7/IntermediateFormsProofFibres.lean`, branch `claude/intermediate-forms-proof`, commit 7b2b7ed2, for the repaired Definition 6.34: intermediate objects of a factorization carry transported forms.)

Finite RV fibres of the target of a relatively unary bijection out of an object.

If `f : A → B` is a bijection out of an object `A` of `μVF^◇[n]` which is relatively
unary in `(i, j)`, then every RV fibre `{t | (y, t) ∈ B}` is finite. The preimage of
`(y, t)` is determined by `y` except for its `i`-th coordinate; by the unary finite
obstacle theorem over the base enlarged by the coordinates of `y`, these `i`-th
coordinates lie in a finite set, since otherwise an open disc around one of them
would produce a second preimage. In degree zero `A` itself is finite. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6.TransportedForms
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

omit [M ⊨ Axioms.ACVF] in
/-- A unary mixed set is definable when its points are cut out by a definable
condition on their raw codes. -/
theorem fibres_mixed_definable_of_codes {S : Set M} {m : ℕ} (X : Set (Mixed M 1 m))
    (R : Set (Fin 1 ⊕ Fin m → M))
    (hR : S.Definable LRV R) (hX : ∀ q, q ∈ X ↔ mixedValues q ∈ R) :
    (rawMixedSpace (M := M) 1 m).Definable S X := by
  change S.Definable LRV ((rawMixedSpace (M := M) 1 m).preimage X)
  convert ((rawMixedSpace (M := M) 1 m).domain_definable.mono (Set.empty_subset S)).inter hR
    using 1
  ext z
  constructor
  · rintro ⟨hz, hzX⟩
    refine ⟨hz, ?_⟩
    have h := (hX _).mp hzX
    rwa [mixedValues_decode] at h
  · rintro ⟨hz, hzR⟩
    refine ⟨hz, (hX _).mpr ?_⟩
    rwa [mixedValues_decode]

/-- The output coordinate carrying the input coordinate `k ≠ i` under a map which is
relatively unary in `(i, j)`. -/
def outIdx {n : ℕ} (i j k : Fin n) : Fin n := (Fin.cycleRange j).symm (Fin.cycleRange i k)

theorem outIdx_ne {n : ℕ} {i j k : Fin n} (hk : k ≠ i) : outIdx i j k ≠ j := by
  intro h
  exact cycleRange_ne_zero hk ((cycleRange_symm_eq_iff j _).mp h)

theorem outIdx_back {n : ℕ} (i j k : Fin n) :
    (Fin.cycleRange i).symm (Fin.cycleRange j (outIdx i j k)) = k := by
  simp only [outIdx, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The input point with `i`-th coordinate `z` whose other coordinates are read off
the output point `y`. -/
def fillPoint {n : ℕ} (i j : Fin n) (y : Fin n → VF M) (z : VF M) : Fin n → VF M :=
  fun k => if k = i then z else y (outIdx i j k)

omit [M ⊨ Axioms.ACVF] in
theorem fillPoint_self {n : ℕ} (i j : Fin n) (y : Fin n → VF M) (z : VF M) :
    fillPoint i j y z i = z := by
  simp only [fillPoint, ite_true]

omit [M ⊨ Axioms.ACVF] in
theorem eq_fillPoint {T : Set M} {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) T}
    {B : DefSet (rawMixedSpace (M := M) n s) T} {f : Map A B} {i j : Fin n}
    (hrel : VFRelativelyUnary f i j) (p : A) {y : Fin n → VF M} (hy : (f p).val.1 = y) :
    p.val.1 = fillPoint i j y (p.val.1 i) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [fillPoint, ite_true]
  · simp only [fillPoint, hk, ite_false]
    have h := hrel p (outIdx i j k) (outIdx_ne hk)
    rw [outIdx_back, hy] at h
    exact h.symm

/-- The unary set of `i`-th coordinates and labels of preimages of points of the
fibre of `B` over `y`. -/
def fibreSet {T : Set M} {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) T}
    {B : DefSet (rawMixedSpace (M := M) n s) T} (f : Map A B) (i j : Fin n)
    (y : Fin n → VF M) : Set (Mixed M 1 (r + s)) :=
  {q | f.graph ((fillPoint i j y (q.1 0), fun a => q.2 (Fin.castAdd s a)) :
      (rawMixedSpace (M := M) n r).Carrier)
    ((y, fun b => q.2 (Fin.natAdd r b)) : (rawMixedSpace (M := M) n s).Carrier)}

omit [M ⊨ Axioms.ACVF] in
theorem fibreSet_definable {T : Set M} {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) T}
    {B : DefSet (rawMixedSpace (M := M) n s) T} (f : Map A B) (i j : Fin n)
    (y : Fin n → VF M) :
    (rawMixedSpace (M := M) 1 (r + s)).Definable (T ∪ Set.range (fun k => (y k).val))
      (fibreSet f i j y) := by
  let T' := T ∪ Set.range (fun k => (y k).val)
  let φ (z : Fin 1 ⊕ Fin (r + s) → M) : (Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s) → M :=
    Sum.elim (Sum.elim (fun k => if k = i then z (.inl 0) else (y (outIdx i j k)).val)
        (fun a => z (.inr (Fin.castAdd s a))))
      (Sum.elim (fun k => (y k).val) (fun b => z (.inr (Fin.natAdd r b))))
  have hφ : T'.DefinableMap LRV φ := by
    rintro ((k | a) | (k | b))
    · by_cases hk : k = i
      · simp only [φ, hk, ite_true, Sum.elim_inl]
        exact Set.DefinableFun.proj LRV
      · simp only [φ, hk, ite_false, Sum.elim_inl]
        exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self _))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self _))
    · exact Set.DefinableFun.proj LRV
  have hG : T'.Definable LRV
      ((rawMixedSpace (M := M) n r).relation (rawMixedSpace (M := M) n s) f.graph) :=
    Set.Definable.mono (f.graph_definable : T.Definable LRV _) Set.subset_union_left
  refine fibres_mixed_definable_of_codes _ _ (hG.preimage_map hφ) ?_
  intro q
  let X : (rawMixedSpace (M := M) n r).Carrier :=
    (fillPoint i j y (q.1 0), fun a => q.2 (Fin.castAdd s a))
  let Y : (rawMixedSpace (M := M) n s).Carrier := (y, fun b => q.2 (Fin.natAdd r b))
  have he : φ (mixedValues q) = Sum.elim (mixedValues X) (mixedValues Y) := by
    funext w
    rcases w with ((k | a) | (k | b))
    · by_cases hk : k = i
      · simp only [φ, X, hk, ite_true, Sum.elim_inl, mixedValues, vfValues, fillPoint]
      · simp only [φ, X, hk, ite_false, Sum.elim_inl, mixedValues, vfValues, fillPoint]
    · rfl
    · rfl
    · rfl
  change f.graph X Y ↔ φ (mixedValues q) ∈
    (rawMixedSpace (M := M) n r).relation (rawMixedSpace (M := M) n s) f.graph
  rw [he]
  have h := Space.relation_decode (rawMixedSpace (M := M) n r) (rawMixedSpace (M := M) n s)
    f.graph ⟨mixedValues X, mixedValues_mem_domain X⟩ ⟨mixedValues Y, mixedValues_mem_domain Y⟩
  rw [decode_mixedValues, decode_mixedValues] at h
  exact h.symm

section Valued

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The valuation of the field sort has a nonzero element of value below `1`. -/
theorem exists_small_nonzero
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ u : VF M, u ≠ 0 ∧ Valued.v u < 1 := by
  obtain ⟨u, hu0, hule⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  refine ⟨u, hu0, lt_of_not_ge ?_⟩
  intro h
  exact hule ((hv 1 u).mpr (by simpa only [map_one] using h))

/-- **Finite RV fibres.** The target of a bijection out of an object which is
relatively unary in `(i, j)` has finite RV fibres. -/
theorem finite_rv_fibres (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {T : Set M} {n s : ℕ} (A : VFObject (M := M) T n)
    (B : DefSet (rawMixedSpace (M := M) n s) T)
    (f : Map A.carrier B) (hbij : Function.Bijective f) {i j : Fin n}
    (hrel : VFRelativelyUnary f i j) :
    ∀ y : Fin n → VF M, {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier}.Finite := by
  intro y
  obtain ⟨Q, -, hQ⟩ := exists_unary_obstacles (G := G) hc hv
    (⟨fibreSet f i j y, fibreSet_definable f i j y⟩ :
      DefSet (rawMixedSpace (M := M) 1 (A.labels + s)) (T ∪ Set.range (fun k => (y k).val)))
  obtain ⟨u0, hu0, hu0v⟩ := exists_small_nonzero (G := G) hv
  -- the `i`-th coordinate of every preimage of a point over `y` is an obstacle
  have key : ∀ p : A.carrier, (f p).val.1 = y → p.val.1 i ∈ Q := by
    intro p hpy
    by_contra hz
    obtain ⟨r0, hr0s, hr0min⟩ := Finset.exists_min_image
      (insert 1 (Q.image (fun q => q - p.val.1 i))) (fun w => (Valued.v w : G))
      (Finset.insert_nonempty _ _)
    have hr0 : r0 ≠ 0 := by
      rcases Finset.mem_insert.mp hr0s with h | h
      · rw [h]
        exact one_ne_zero
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
        intro h0
        exact hz (sub_eq_zero.mp h0 ▸ hq)
    have hvr0 : (Valued.v r0 : G) ≠ 0 := (map_ne_zero _).mpr hr0
    let ρ := Balls.openRadius (Valued.v r0) hvr0
    have havoid : ∀ q ∈ Q, q ∉ Balls.openDisc Valued.v (p.val.1 i) ρ := by
      intro q hq hqd
      rw [Balls.openDisc_openRadius] at hqd
      have hle := hr0min (q - p.val.1 i)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq))
      exact absurd hqd (not_lt.mpr hle)
    have hz_mem : p.val.1 i ∈ Balls.openDisc Valued.v (p.val.1 i) ρ :=
      Balls.centre_mem_openDisc _ _ _
    have hy_mem : p.val.1 i + r0 * u0 ∈ Balls.openDisc Valued.v (p.val.1 i) ρ := by
      rw [Balls.openDisc_openRadius]
      change Valued.v (p.val.1 i + r0 * u0 - p.val.1 i) < Valued.v r0
      rw [add_sub_cancel_left, map_mul]
      exact mul_lt_of_lt_one_right (zero_lt_iff.mpr hvr0) hu0v
    have hC := hQ (p.val.1 i) ρ havoid (p.val.1 i) hz_mem (p.val.1 i + r0 * u0) hy_mem
      (Fin.append p.val.2 (f p).val.2)
    have hmem : ((fun _ : Fin 1 => p.val.1 i), Fin.append p.val.2 (f p).val.2) ∈
        fibreSet f i j y := by
      change f.graph _ _
      simp only [Fin.append_left, Fin.append_right]
      rw [← eq_fillPoint hrel p hpy, ← hpy]
      exact ⟨p, rfl, rfl⟩
    obtain ⟨a, ha, hfa⟩ := hC.mp hmem
    simp only [Fin.append_left, Fin.append_right] at ha hfa
    have hfeq : f a = f p := Subtype.ext (hfa.trans (by rw [← hpy]; rfl))
    have hap : a.val.1 i = p.val.1 i := congrArg (fun w : A.carrier => w.val.1 i) (hbij.1 hfeq)
    rw [ha] at hap
    simp only [fillPoint_self] at hap
    exact mul_ne_zero hr0 hu0 (add_eq_left.mp hap)
  -- finitely many preimage data
  let P : Set (VF M × (Fin A.labels → RVInfinity M)) := (Q : Set (VF M)) ×ˢ
    ⋃ q ∈ Q, {u | (fillPoint i j y q, u) ∈ A.carrier.carrier}
  have hP : P.Finite := Q.finite_toSet.prod
    (Set.Finite.biUnion Q.finite_toSet (fun q _ => A.finiteRV _))
  have hpre : ∀ t : {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier},
      ∃ p : A.carrier, (f p).val = (y, t.val) := by
    intro t
    obtain ⟨p, hp⟩ := hbij.2 ⟨(y, t.val), t.property⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  choose pre hpre using hpre
  have hmemP (t : {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier}) :
      ((pre t).val.1 i, (pre t).val.2) ∈ P := by
    have hy : (f (pre t)).val.1 = y := by rw [hpre t]
    have hq := key (pre t) hy
    refine ⟨hq, Set.mem_biUnion hq ?_⟩
    change (fillPoint i j y ((pre t).val.1 i), (pre t).val.2) ∈ A.carrier.carrier
    rw [← eq_fillPoint hrel (pre t) hy]
    exact (pre t).property
  let g (t : {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier}) : P := ⟨_, hmemP t⟩
  have hg : Function.Injective g := by
    intro t t' htt
    have h1 := congrArg (fun w : P => w.val.1) htt
    have h2 := congrArg (fun w : P => w.val.2) htt
    simp only [g] at h1 h2
    have hy : (f (pre t)).val.1 = y := by rw [hpre t]
    have hy' : (f (pre t')).val.1 = y := by rw [hpre t']
    have hpp : pre t = pre t' := by
      apply Subtype.ext
      refine Prod.ext ?_ h2
      rw [eq_fillPoint hrel (pre t) hy, eq_fillPoint hrel (pre t') hy', h1]
    have h := (hpre t).symm.trans ((congrArg (fun w => (f w).val) hpp).trans (hpre t'))
    exact Subtype.ext (congrArg Prod.snd h)
  have := hP.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

end Valued

/-- **Finite RV fibres in degree zero.** The target of a bijection out of an object
of `μVF^◇[0]` is finite, so it has finite RV fibres. -/
theorem finite_rv_fibres_zero {T : Set M} {s : ℕ} (A : VFObject (M := M) T 0)
    (B : DefSet (rawMixedSpace (M := M) 0 s) T) (f : Map A.carrier B)
    (hbij : Function.Bijective f) :
    ∀ y : Fin 0 → VF M, {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier}.Finite := by
  intro y
  have hA : (A.carrier.carrier).Finite := by
    have h := (A.finiteRV y).image (fun t => ((y, t) : Mixed M 0 A.labels))
    refine h.subset ?_
    intro p hp
    refine ⟨p.2, ?_, ?_⟩
    · change (y, p.2) ∈ A.carrier.carrier
      rw [Subsingleton.elim y p.1]
      exact hp
    · exact Prod.ext (Subsingleton.elim _ _) rfl
  have := hA.to_subtype
  refine (Set.finite_range (fun p : A.carrier => (f p).val.2)).subset ?_
  intro t ht
  obtain ⟨p, hp⟩ := hbij.2 ⟨(y, t), ht⟩
  exact ⟨p, congrArg (fun w : B => w.val.2) hp⟩

end DiamondIntegral.Section6.TransportedForms
