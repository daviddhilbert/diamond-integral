import «section 8».TruncPairs

/-! Correspondences between truncations of sets of different dimensions.

`TruncPairs` compares the truncations of two sets of the same dimension `n` at the same cutoffs.
Here `X ⊆ VF^n × RV^l` is truncated at the cutoffs `b` and `Y ⊆ VF^{n'} × RV^{l'}` at the cutoffs
`b'`. The class `Θ([X[m;b]])` without the normalization `[𝔸]^{-mΣb}` is `rawClass`
(`fullClass_eq_rawClass`).

* `pairTrunc_relation_definableG`: for a set `W` of pairs `(p, p')`, definable over `ℂ((t))` and
  invariant at the cutoffs `(b, b')`, the relation `{(p[m;b], p'[m;b']) | (p, p') ∈ W}` is definable.
* `rawClass_eq_of_correspondence`, `rawClass_eq_of_thickened`: a map `Φ` of the rational integral
  points of `X` onto those of `Y`, such that two points have the same truncation iff their images do,
  with a definable thickened graph, gives `Θ([X[m;b]]) = Θ([Y[m;b']])`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm

local instance pairGStructure : LRV.Structure Carrier := canonicalInterpret
local instance pairGModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable {n n' l l' : ℕ} (m : ℕ+) (b : Fin n → ℕ) (b' : Fin n' → ℕ)

/-! ### Pairs of points -/

/-- The pair of two points, as one point. -/
def joinG {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n' → Ser) × (Fin k' → RV)) :
    (Fin (n + n') → Ser) × (Fin (k + k') → RV) :=
  (Fin.append p.1 p'.1, Fin.append p.2 p'.2)

/-- The first point of a pair. -/
def leftG {k k' : ℕ} (q : (Fin (n + n') → Ser) × (Fin (k + k') → RV)) : (Fin n → Ser) × (Fin k → RV) :=
  (fun i => q.1 (Fin.castAdd n' i), fun j => q.2 (Fin.castAdd k' j))

/-- The second point of a pair. -/
def rightG {k k' : ℕ} (q : (Fin (n + n') → Ser) × (Fin (k + k') → RV)) : (Fin n' → Ser) × (Fin k' → RV) :=
  (fun i => q.1 (Fin.natAdd n i), fun j => q.2 (Fin.natAdd k j))

theorem joinG_left_right {k k' : ℕ} (q : (Fin (n + n') → Ser) × (Fin (k + k') → RV)) :
    joinG (leftG q) (rightG q) = q :=
  Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

theorem RI_joinG {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n' → Ser) × (Fin k' → RV)) :
    RI m (joinG p p') ↔ RI m p ∧ RI m p' := by
  simp only [RI, joinG, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  tauto

/-! ### Truncation coordinates of a pair -/

/-- Splitting a truncation index for the cutoffs `(b, b')`. -/
def splitIdxG (k : Idx (Fin.append b b')) : Idx b ⊕ Idx b' :=
  if h : (k.1 : ℕ) < n then
    .inl ⟨⟨k.1, h⟩, ⟨k.2, by have := k.2.isLt; have e := append_lt b b' k.1 h; omega⟩⟩
  else
    .inr ⟨⟨k.1 - n, by have := k.1.isLt; omega⟩,
      ⟨k.2, by have := k.2.isLt; have e := append_ge b b' k.1 h; omega⟩⟩

theorem truncPoint_splitG (x : Fin n → Ser) (x' : Fin n' → Ser) (k : Idx (Fin.append b b')) :
    truncPoint m (Fin.append b b') (Fin.append x x') k =
      Sum.elim (truncPoint m b x) (truncPoint m b' x') (splitIdxG b b' k) := by
  unfold splitIdxG
  split_ifs with h
  · simp only [Sum.elim_inl, truncPoint]
    rw [append_lt x x' k.1 h]
  · simp only [Sum.elim_inr, truncPoint]
    rw [append_ge x x' k.1 h]

theorem splitIdxG_surjective : Function.Surjective (splitIdxG b b') := by
  rintro (⟨i, j⟩ | ⟨i, j⟩)
  · refine ⟨⟨Fin.castAdd n' i, ⟨j, by rw [Fin.append_left]; exact j.isLt⟩⟩, ?_⟩
    unfold splitIdxG
    split_ifs with h
    · rfl
    · exact absurd i.isLt (by simp at h)
  · refine ⟨⟨Fin.natAdd n i, ⟨j, by rw [Fin.append_right]; exact j.isLt⟩⟩, ?_⟩
    unfold splitIdxG
    split_ifs with h
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (idx_eq b' (Fin.ext (by simp)) _ _ rfl)

/-- The truncation coordinates of a pair, sent to those of its two points. -/
def shuffleG {k k' : ℕ} : Idx (Fin.append b b') ⊕ Fin (k + k') → (Idx b ⊕ Fin k) ⊕ (Idx b' ⊕ Fin k') :=
  Sum.elim (fun c => Sum.map Sum.inl Sum.inl (splitIdxG b b' c))
    (fun j => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm j))

theorem shuffleG_surjective {k k' : ℕ} : Function.Surjective (shuffleG (k := k) (k' := k') b b') := by
  rintro ((c | j) | (c | j))
  · obtain ⟨d, hd⟩ := splitIdxG_surjective b b' (.inl c)
    exact ⟨.inl d, by simp [shuffleG, hd]⟩
  · exact ⟨.inr (Fin.castAdd k' j), by simp [shuffleG]⟩
  · obtain ⟨d, hd⟩ := splitIdxG_surjective b b' (.inr c)
    exact ⟨.inl d, by simp [shuffleG, hd]⟩
  · exact ⟨.inr (Fin.natAdd k j), by simp [shuffleG]⟩

theorem trunc_shuffleG {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n' → Ser) × (Fin k' → RV))
    (c : Idx (Fin.append b b') ⊕ Fin (k + k')) :
    Sum.elim (truncPoint m (Fin.append b b') (joinG p p').1) (joinG p p').2 c =
      Sum.elim (Sum.elim (truncPoint m b p.1) p.2) (Sum.elim (truncPoint m b' p'.1) p'.2) (shuffleG b b' c) := by
  rcases c with c | j
  · simp only [Sum.elim_inl, shuffleG, joinG]
    rw [truncPoint_splitG]
    rcases splitIdxG b b' c with d | d <;> rfl
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;> simp [shuffleG, joinG]

/-- The truncation coordinates of a pair, as coordinates of the two truncations. -/
def tauIdxG {k k' : ℕ} (a : Fin (Kt (Fin.append b b') (k + k'))) : Fin (Kt b k) ⊕ Fin (Kt b' k') :=
  Sum.map (εt b k) (εt b' k') (shuffleG b b' ((εt (Fin.append b b') (k + k')).symm a))

theorem tauIdxG_surjective {k k' : ℕ} : Function.Surjective (tauIdxG (k := k) (k' := k') b b') := by
  intro y
  obtain ⟨y0, rfl⟩ : ∃ y0, Sum.map (εt b k) (εt b' k') y0 = y := by
    rcases y with y | y
    · exact ⟨.inl ((εt b k).symm y), by simp⟩
    · exact ⟨.inr ((εt b' k').symm y), by simp⟩
  obtain ⟨c, rfl⟩ := shuffleG_surjective b b' y0
  exact ⟨εt (Fin.append b b') (k + k') c, by simp [tauIdxG]⟩

theorem truncOf_joinG {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n' → Ser) × (Fin k' → RV))
    (a : Fin (Kt (Fin.append b b') (k + k'))) :
    truncOf m (Fin.append b b') (joinG p p') a =
      Sum.elim (truncOf m b p) (truncOf m b' p') (tauIdxG b b' a) := by
  unfold truncOf tauIdxG
  rw [trunc_shuffleG]
  rcases shuffleG b b' ((εt (Fin.append b b') (k + k')).symm a) with d | d <;>
    simp [Equiv.symm_apply_apply]

/-- **The relation on truncations induced by a set of pairs is definable.** -/
theorem pairTrunc_relation_definableG (Q : Finset (Fin (l + l') → ℤ))
    {W : Set (Fin ((n + n') + (l + l')) → Carrier)}
    (hW : DefinableOver {c | baseCarrier c} (mixedSorts (n + n') (l + l')) W)
    (hA : Invariant m (Fin.append b b') (mixedSet W)) (hQ : Covers m Q (mixedSet W)) :
    (rawRVSpace (M := Carrier) (Kt b l)).RelationDefinable (rawRVSpace (M := Carrier) (Kt b' l'))
      {c | baseCarrier c} (fun r r' => ∃ p p', joinG p p' ∈ mixedSet W ∧ RI m p ∧ RI m p' ∧
        r = truncOf m b p ∧ r' = truncOf m b' p') := by
  refine rawRV_relation_definable_of (tauIdxG b b') (tauIdxG_surjective b b')
    (fullTruncSet_definable m (Fin.append b b') Q hW hA hQ) _ fun x y => ?_
  rw [mem_fullTruncSet_iff]
  constructor
  · rintro ⟨p, p', hW', hp, hp', rfl, rfl⟩
    refine ⟨joinG p p', hW', (RI_joinG m p p').mpr ⟨hp, hp'⟩, ?_⟩
    funext a
    rw [truncOf_joinG]
  · rintro ⟨q, hq, hRI, hxy⟩
    obtain ⟨p, p', rfl⟩ : ∃ p p', q = joinG p p' := ⟨leftG q, rightG q, (joinG_left_right q).symm⟩
    obtain ⟨hp, hp'⟩ := (RI_joinG m p p').mp hRI
    refine ⟨p, p', hq, hp, hp', ?_, ?_⟩
    · funext c
      obtain ⟨a, ha⟩ := tauIdxG_surjective b b' (.inl c)
      have := congrFun hxy a
      rw [truncOf_joinG, ha] at this
      exact this
    · funext c
      obtain ⟨a, ha⟩ := tauIdxG_surjective b b' (.inr c)
      have := congrFun hxy a
      rw [truncOf_joinG, ha] at this
      exact this

/-- Label patterns of pairs. -/
def pairPatternsG (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ)) : Finset (Fin (l + l') → ℤ) :=
  (Q ×ˢ Q').image (fun qq => Fin.append qq.1 qq.2)

variable {X : Set (Fin (n + l) → Carrier)} {Y : Set (Fin (n' + l') → Carrier)}

theorem covers_pairsG {Q : Finset (Fin l → ℤ)} {Q' : Finset (Fin l' → ℤ)}
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    {W : Set (Fin ((n + n') + (l + l')) → Carrier)}
    (hW : ∀ p p', joinG p p' ∈ mixedSet W → RI m p → RI m p' → p ∈ mixedSet X ∧ p' ∈ mixedSet Y) :
    Covers m (pairPatternsG Q Q') (mixedSet W) := by
  intro q hq hr hu
  obtain ⟨p, p', rfl⟩ : ∃ p p', q = joinG p p' := ⟨leftG q, rightG q, (joinG_left_right q).symm⟩
  obtain ⟨hp, hp'⟩ := (RI_joinG m p p').mp ⟨hr, hu⟩
  obtain ⟨hX, hY⟩ := hW p p' hq hp hp'
  obtain ⟨q1, hq1, h1⟩ := hQ p hX hp.1 hp.2
  obtain ⟨q2, hq2, h2⟩ := hQ' p' hY hp'.1 hp'.2
  refine ⟨Fin.append q1 q2, Finset.mem_image.mpr ⟨(q1, q2), Finset.mem_product.mpr ⟨hq1, hq2⟩, rfl⟩, ?_⟩
  intro j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · simp only [joinG, Fin.append_left]
    exact h1 a
  · simp only [joinG, Fin.append_right]
    exact h2 a

/-! ### The unnormalized class -/

/-- `Θ([X[m;b]])`, without the normalization `[𝔸]^{-mΣb}`. -/
def rawClass (Q : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) : Rloc :=
  algebraMap EquivariantVariety.ModifiedRing Rloc
    (theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
      (resSetClass canonicalInterpret_isCanonical (fullTruncDefSet m b Q hX hA hQ)
        (fullTruncSet_finite_values m b Q hX hA hQ))))

theorem fullClass_eq_rawClass (Q : Finset (Fin l → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) :
    fullClass m b Q hX hA hQ = rawClass m b Q hX hA hQ * Linv (∑ i, b i) := rfl

/-- **Invariance of truncation classes, in different dimensions.** -/
theorem rawClass_eq_of_correspondence
    (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hY : DefinableOver {c | baseCarrier c} (mixedSorts n' l') Y)
    (hA : Invariant m b (mixedSet X)) (hB : Invariant m b' (mixedSet Y))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    (Φ : (Fin n → Ser) × (Fin l → RV) → (Fin n' → Ser) × (Fin l' → RV))
    (hmaps : ∀ p ∈ mixedSet X, RI m p → Φ p ∈ mixedSet Y ∧ RI m (Φ p))
    (hsurj : ∀ p' ∈ mixedSet Y, RI m p' → ∃ p ∈ mixedSet X, RI m p ∧ Φ p = p')
    (hresp : ∀ p ∈ mixedSet X, ∀ p' ∈ mixedSet X, RI m p → RI m p' →
      (truncOf m b p = truncOf m b p' ↔ truncOf m b' (Φ p) = truncOf m b' (Φ p')))
    (hgraph : (rawRVSpace (M := Carrier) (Kt b l)).RelationDefinable (rawRVSpace (M := Carrier) (Kt b' l'))
      {c | baseCarrier c} (fun r r' => ∃ p ∈ mixedSet X, RI m p ∧ r = truncOf m b p ∧ r' = truncOf m b' (Φ p))) :
    rawClass m b Q hX hA hQ = rawClass m b' Q' hY hB hQ' := by
  let SX := fullTruncDefSet m b Q hX hA hQ
  let SY := fullTruncDefSet m b' Q' hY hB hQ'
  have hpt : ∀ r : SX, ∃ p ∈ mixedSet X, RI m p ∧ r.val = truncOf m b p :=
    fun r => (mem_fullTruncSet_iff m b _ r.val).mp r.property
  choose pt hptX hptRI hptEq using hpt
  let F : SX → SY := fun r => ⟨truncOf m b' (Φ (pt r)),
    (mem_fullTruncSet_iff m b' _ _).mpr ⟨Φ (pt r), (hmaps _ (hptX r) (hptRI r)).1,
      (hmaps _ (hptX r) (hptRI r)).2, rfl⟩⟩
  have hF : ∀ (r : SX) (p : (Fin n → Ser) × (Fin l → RV)), p ∈ mixedSet X → RI m p →
      r.val = truncOf m b p → (F r).val = truncOf m b' (Φ p) := by
    intro r p hp hRI hr
    exact (hresp _ (hptX r) _ hp (hptRI r) hRI).mp ((hptEq r).symm.trans hr)
  let f : Map SX SY := ⟨F, by
    refine (hgraph.congr _ _ ?_)
    intro r r'
    constructor
    · rintro ⟨p, hp, hRI, rfl, rfl⟩
      have hr : truncOf m b p ∈ SX.carrier := (mem_fullTruncSet_iff m b _ _).mpr ⟨p, hp, hRI, rfl⟩
      exact ⟨⟨_, hr⟩, rfl, hF ⟨_, hr⟩ p hp hRI rfl⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨pt a, hptX a, hptRI a, hptEq a, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      have h1 : (F r).val = (F s).val := congrArg Subtype.val hrs
      rw [hptEq r, hptEq s]
      exact (hresp _ (hptX r) _ (hptX s) (hptRI r) (hptRI s)).mpr h1
    · intro s
      obtain ⟨p', hp', hRI', hs⟩ := (mem_fullTruncSet_iff m b' _ s.val).mp s.property
      obtain ⟨p, hp, hRI, rfl⟩ := hsurj p' hp' hRI'
      have hr : truncOf m b p ∈ SX.carrier := (mem_fullTruncSet_iff m b _ _).mpr ⟨p, hp, hRI, rfl⟩
      exact ⟨⟨_, hr⟩, Subtype.ext ((hF ⟨_, hr⟩ p hp hRI rfl).trans hs.symm)⟩
  have hcls := resSetClass_bijection canonicalInterpret_isCanonical SX SY
    (fullTruncSet_finite_values m b Q hX hA hQ) (fullTruncSet_finite_values m b' Q' hY hB hQ') ⟨f, hbij⟩
  unfold rawClass
  rw [hcls]

/-- **Invariance of truncation classes through a thickened graph, in different dimensions.** `W` is
a set of pairs, definable over `ℂ((t))` and `(b, b')`-invariant, containing `(p, Φ p)` for the
rational integral points of `X`, and whose rational integral pairs `(p, p')` have `p ∈ X`, `p' ∈ Y`
and `p'[m;b'] = (Φ p)[m;b']`. -/
theorem rawClass_eq_of_thickened
    (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hY : DefinableOver {c | baseCarrier c} (mixedSorts n' l') Y)
    (hA : Invariant m b (mixedSet X)) (hB : Invariant m b' (mixedSet Y))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    (Φ : (Fin n → Ser) × (Fin l → RV) → (Fin n' → Ser) × (Fin l' → RV))
    (hmaps : ∀ p ∈ mixedSet X, RI m p → Φ p ∈ mixedSet Y ∧ RI m (Φ p))
    (hsurj : ∀ p' ∈ mixedSet Y, RI m p' → ∃ p ∈ mixedSet X, RI m p ∧ Φ p = p')
    (hresp : ∀ p ∈ mixedSet X, ∀ p' ∈ mixedSet X, RI m p → RI m p' →
      (truncOf m b p = truncOf m b p' ↔ truncOf m b' (Φ p) = truncOf m b' (Φ p')))
    (W : Set (Fin ((n + n') + (l + l')) → Carrier))
    (hW : DefinableOver {c | baseCarrier c} (mixedSorts (n + n') (l + l')) W)
    (hWA : Invariant m (Fin.append b b') (mixedSet W))
    (hW1 : ∀ p p', joinG p p' ∈ mixedSet W → RI m p → RI m p' →
      p ∈ mixedSet X ∧ p' ∈ mixedSet Y ∧ truncOf m b' p' = truncOf m b' (Φ p))
    (hW2 : ∀ p ∈ mixedSet X, RI m p → joinG p (Φ p) ∈ mixedSet W) :
    rawClass m b Q hX hA hQ = rawClass m b' Q' hY hB hQ' := by
  have hWQ := covers_pairsG m hQ hQ' (fun p p' h hp hp' => ⟨(hW1 p p' h hp hp').1, (hW1 p p' h hp hp').2.1⟩)
  refine rawClass_eq_of_correspondence m b b' Q Q' hX hY hA hB hQ hQ' Φ hmaps hsurj hresp
    ((pairTrunc_relation_definableG m b b' _ hW hWA hWQ).congr _ _ fun r r' => ?_)
  constructor
  · rintro ⟨p, p', hW', hp, hp', rfl, rfl⟩
    exact ⟨p, (hW1 p p' hW' hp hp').1, hp, rfl, (hW1 p p' hW' hp hp').2.2⟩
  · rintro ⟨p, hp, hRI, rfl, rfl⟩
    exact ⟨p, Φ p, hW2 p hp hRI, hRI, (hmaps p hp hRI).2, rfl, rfl⟩

end DiamondIntegral.Section8.Truncation
