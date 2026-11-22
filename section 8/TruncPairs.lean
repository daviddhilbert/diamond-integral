import «section 8».TruncGraph

/-! The relation on truncations induced by a set of pairs.

For a set `W` of pairs `(p, p')` of concrete points (VF coordinates `n + n`, labels `l + l'`), the
truncation of `W` at the cutoffs `(β, β)` is the set of pairs of truncations, up to a coordinate
permutation (`truncOf_join`). Hence (`pairTrunc_relation_definable`) the relation
`{(p[m;β], p'[m;β]) | (p, p') ∈ W}` is definable over `ℂ((t))` whenever `W` is, and
(`fullClass_eq_of_thickened`) a correspondence between `X` and `Y` whose thickened graph
`W ∋ (p, p')`, `p' ≡ Φ p mod 𝔪_β`, is definable preserves the truncation class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

local instance pairStructure : LRV.Structure Carrier := canonicalInterpret
local instance pairModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

theorem append_lt {α : Type*} {a c : ℕ} (f : Fin a → α) (g : Fin c → α) (i : Fin (a + c))
    (h : (i : ℕ) < a) : Fin.append f g i = f ⟨i, h⟩ := by
  have e : i = Fin.castAdd c ⟨i, h⟩ := Fin.ext rfl
  conv_lhs => rw [e]
  rw [Fin.append_left]

theorem append_ge {α : Type*} {a c : ℕ} (f : Fin a → α) (g : Fin c → α) (i : Fin (a + c))
    (h : ¬ (i : ℕ) < a) : Fin.append f g i = g ⟨i - a, by have := i.isLt; omega⟩ := by
  have e : i = Fin.natAdd a ⟨i - a, by have := i.isLt; omega⟩ := Fin.ext (by simp; omega)
  conv_lhs => rw [e]
  rw [Fin.append_right]

variable {n l l' : ℕ} (m : ℕ+) (b : Fin n → ℕ)

/-! ### Pairs of points -/

/-- The pair of two points, as one point. -/
def joinP {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n → Ser) × (Fin k' → RV)) :
    (Fin (n + n) → Ser) × (Fin (k + k') → RV) :=
  (Fin.append p.1 p'.1, Fin.append p.2 p'.2)

/-- The first point of a pair. -/
def leftP {k k' : ℕ} (q : (Fin (n + n) → Ser) × (Fin (k + k') → RV)) : (Fin n → Ser) × (Fin k → RV) :=
  (fun i => q.1 (Fin.castAdd n i), fun j => q.2 (Fin.castAdd k' j))

/-- The second point of a pair. -/
def rightP {k k' : ℕ} (q : (Fin (n + n) → Ser) × (Fin (k + k') → RV)) : (Fin n → Ser) × (Fin k' → RV) :=
  (fun i => q.1 (Fin.natAdd n i), fun j => q.2 (Fin.natAdd k j))

theorem join_left_right {k k' : ℕ} (q : (Fin (n + n) → Ser) × (Fin (k + k') → RV)) :
    joinP (leftP q) (rightP q) = q :=
  Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

theorem RI_join {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n → Ser) × (Fin k' → RV)) :
    RI m (joinP p p') ↔ RI m p ∧ RI m p' := by
  simp only [RI, joinP, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  tauto

/-! ### Truncation coordinates of a pair -/

theorem idx_eq {i i' : Fin n} (h : i = i') (j : Fin (b i + 1)) (j' : Fin (b i' + 1)) (hj : (j : ℕ) = j') :
    (⟨i, j⟩ : Idx b) = ⟨i', j'⟩ := by
  subst h
  exact congrArg _ (Fin.ext hj)

/-- Splitting a truncation index for the cutoffs `(β, β)`. -/
def splitIdx (k : Idx (Fin.append b b)) : Idx b ⊕ Idx b :=
  if h : (k.1 : ℕ) < n then
    .inl ⟨⟨k.1, h⟩, ⟨k.2, by have := k.2.isLt; have e := append_lt b b k.1 h; omega⟩⟩
  else
    .inr ⟨⟨k.1 - n, by have := k.1.isLt; omega⟩,
      ⟨k.2, by have := k.2.isLt; have e := append_ge b b k.1 h; omega⟩⟩

theorem truncPoint_split (x x' : Fin n → Ser) (k : Idx (Fin.append b b)) :
    truncPoint m (Fin.append b b) (Fin.append x x') k =
      Sum.elim (truncPoint m b x) (truncPoint m b x') (splitIdx b k) := by
  unfold splitIdx
  split_ifs with h
  · simp only [Sum.elim_inl, truncPoint]
    rw [append_lt x x' k.1 h]
  · simp only [Sum.elim_inr, truncPoint]
    rw [append_ge x x' k.1 h]

theorem splitIdx_surjective : Function.Surjective (splitIdx b) := by
  rintro (⟨i, j⟩ | ⟨i, j⟩)
  · refine ⟨⟨Fin.castAdd n i, ⟨j, by rw [Fin.append_left]; exact j.isLt⟩⟩, ?_⟩
    unfold splitIdx
    split_ifs with h
    · rfl
    · exact absurd i.isLt (by simp at h)
  · refine ⟨⟨Fin.natAdd n i, ⟨j, by rw [Fin.append_right]; exact j.isLt⟩⟩, ?_⟩
    unfold splitIdx
    split_ifs with h
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (idx_eq b (Fin.ext (by simp)) _ _ rfl)

/-- The truncation coordinates of a pair, sent to those of its two points. -/
def shuffle {k k' : ℕ} : Idx (Fin.append b b) ⊕ Fin (k + k') → (Idx b ⊕ Fin k) ⊕ (Idx b ⊕ Fin k') :=
  Sum.elim (fun c => Sum.map Sum.inl Sum.inl (splitIdx b c))
    (fun j => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm j))

theorem shuffle_surjective {k k' : ℕ} : Function.Surjective (shuffle (k := k) (k' := k') b) := by
  rintro ((c | j) | (c | j))
  · obtain ⟨d, hd⟩ := splitIdx_surjective b (.inl c)
    exact ⟨.inl d, by simp [shuffle, hd]⟩
  · exact ⟨.inr (Fin.castAdd k' j), by simp [shuffle]⟩
  · obtain ⟨d, hd⟩ := splitIdx_surjective b (.inr c)
    exact ⟨.inl d, by simp [shuffle, hd]⟩
  · exact ⟨.inr (Fin.natAdd k j), by simp [shuffle]⟩

theorem trunc_shuffle {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n → Ser) × (Fin k' → RV))
    (c : Idx (Fin.append b b) ⊕ Fin (k + k')) :
    Sum.elim (truncPoint m (Fin.append b b) (joinP p p').1) (joinP p p').2 c =
      Sum.elim (Sum.elim (truncPoint m b p.1) p.2) (Sum.elim (truncPoint m b p'.1) p'.2) (shuffle b c) := by
  rcases c with c | j
  · simp only [Sum.elim_inl, shuffle, joinP]
    rw [truncPoint_split]
    rcases splitIdx b c with d | d <;> rfl
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;> simp [shuffle, joinP]

/-- The truncation coordinates of a pair, as coordinates of the two truncations. -/
def tauIdx {k k' : ℕ} (a : Fin (Kt (Fin.append b b) (k + k'))) : Fin (Kt b k) ⊕ Fin (Kt b k') :=
  Sum.map (εt b k) (εt b k') (shuffle b ((εt (Fin.append b b) (k + k')).symm a))

theorem tauIdx_surjective {k k' : ℕ} : Function.Surjective (tauIdx (k := k) (k' := k') b) := by
  intro y
  obtain ⟨y0, rfl⟩ : ∃ y0, Sum.map (εt b k) (εt b k') y0 = y := by
    rcases y with y | y
    · exact ⟨.inl ((εt b k).symm y), by simp⟩
    · exact ⟨.inr ((εt b k').symm y), by simp⟩
  obtain ⟨c, rfl⟩ := shuffle_surjective b y0
  exact ⟨εt (Fin.append b b) (k + k') c, by simp [tauIdx]⟩

theorem truncOf_join {k k' : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) (p' : (Fin n → Ser) × (Fin k' → RV))
    (a : Fin (Kt (Fin.append b b) (k + k'))) :
    truncOf m (Fin.append b b) (joinP p p') a = Sum.elim (truncOf m b p) (truncOf m b p') (tauIdx b a) := by
  unfold truncOf tauIdx
  rw [trunc_shuffle]
  rcases shuffle b ((εt (Fin.append b b) (k + k')).symm a) with d | d <;>
    simp [Equiv.symm_apply_apply]

/-! ### Membership in raw RV spaces -/

theorem rawRV_preimage_iff {K : ℕ} (A : Set (Fin K → CanonicalRV.RVSort Carrier)) (z : Fin K → Carrier) :
    z ∈ (rawRVSpace (M := Carrier) K).preimage A ↔ ∃ x ∈ A, rvValues x = z := by
  constructor
  · rintro ⟨hz, hA⟩
    exact ⟨_, hA, Classical.choose_spec hz⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hd : (rawRVSpace (M := Carrier) K).decode ⟨rvValues x, ⟨x, rfl⟩⟩ = x :=
      rvValues_injective (Classical.choose_spec (⟨x, rfl⟩ : rvValues x ∈ Set.range (rvValues (M := Carrier))))
    rw [hd]
    exact hx

theorem rawRV_relation_iff {K K' : ℕ}
    (r : (Fin K → CanonicalRV.RVSort Carrier) → (Fin K' → CanonicalRV.RVSort Carrier) → Prop)
    (z : Fin K ⊕ Fin K' → Carrier) :
    z ∈ (rawRVSpace (M := Carrier) K).relation (rawRVSpace (M := Carrier) K') r ↔
      ∃ x y, r x y ∧ rvValues x = z ∘ Sum.inl ∧ rvValues y = z ∘ Sum.inr := by
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨_, _, h, Classical.choose_spec hx, Classical.choose_spec hy⟩
  · rintro ⟨x, y, h, hx, hy⟩
    have hx' : z ∘ Sum.inl ∈ (rawRVSpace (M := Carrier) K).domain := ⟨x, hx⟩
    have hy' : z ∘ Sum.inr ∈ (rawRVSpace (M := Carrier) K').domain := ⟨y, hy⟩
    refine ⟨hx', hy', ?_⟩
    have dx : (rawRVSpace (M := Carrier) K).decode ⟨z ∘ Sum.inl, hx'⟩ = x :=
      rvValues_injective ((Classical.choose_spec hx').trans hx.symm)
    have dy : (rawRVSpace (M := Carrier) K').decode ⟨z ∘ Sum.inr, hy'⟩ = y :=
      rvValues_injective ((Classical.choose_spec hy').trans hy.symm)
    rw [dx, dy]
    exact h

/-! ### The relation on truncations -/

/-- A relation whose pairs, reindexed by a surjection `τ`, form a definable set, is definable. -/
theorem rawRV_relation_definable_of {K K' K0 : ℕ} (τ : Fin K0 → Fin K ⊕ Fin K')
    (hτ : Function.Surjective τ) {S : Set (Fin K0 → CanonicalRV.RVSort Carrier)}
    (hS : (rawRVSpace (M := Carrier) K0).Definable {c | baseCarrier c} S)
    (R : (Fin K → CanonicalRV.RVSort Carrier) → (Fin K' → CanonicalRV.RVSort Carrier) → Prop)
    (hR : ∀ x y, R x y ↔ (fun a => Sum.elim x y (τ a)) ∈ S) :
    (rawRVSpace (M := Carrier) K).RelationDefinable (rawRVSpace (M := Carrier) K') {c | baseCarrier c} R := by
  have hS' : {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) K0).preimage S) := hS
  have h := hS'.preimage_comp τ
  have he : (rawRVSpace (M := Carrier) K).relation (rawRVSpace (M := Carrier) K') R =
      (fun g : Fin K ⊕ Fin K' → Carrier => g ∘ τ) ⁻¹' (rawRVSpace (M := Carrier) K0).preimage S := by
    apply Set.ext
    intro (z : Fin K ⊕ Fin K' → Carrier)
    rw [rawRV_relation_iff, Set.mem_preimage, rawRV_preimage_iff]
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      refine ⟨_, (hR x y).mp hxy, ?_⟩
      funext a
      change (Sum.elim x y (τ a)).val = z (τ a)
      rcases τ a with c | c
      · exact congrFun hx c
      · exact congrFun hy c
    · rintro ⟨w, hw, hwz⟩
      have hw' : ∀ a, (w a).val = z (τ a) := fun a => congrFun hwz a
      have hz : ∀ c : Fin K ⊕ Fin K', ∃ r : CanonicalRV.RVSort Carrier, r.val = z c := by
        intro c
        obtain ⟨a, rfl⟩ := hτ c
        exact ⟨w a, hw' a⟩
      choose x hx using hz
      refine ⟨fun c => x (.inl c), fun c => x (.inr c), (hR _ _).mpr ?_, funext fun c => hx _,
        funext fun c => hx _⟩
      have hxw : (fun a => Sum.elim (fun c => x (.inl c)) (fun c => x (.inr c)) (τ a)) = w := by
        funext a
        apply Subtype.ext
        rw [hw' a]
        generalize τ a = c
        rcases c with c | c <;> exact hx _
      rw [hxw]
      exact hw
  change {c | baseCarrier c}.Definable LRV
    ((rawRVSpace (M := Carrier) K).relation (rawRVSpace (M := Carrier) K') R)
  rw [he]
  exact h

/-- **The relation on truncations induced by a set of pairs is definable.** -/
theorem pairTrunc_relation_definable (Q : Finset (Fin (l + l') → ℤ))
    {W : Set (Fin ((n + n) + (l + l')) → Carrier)}
    (hW : DefinableOver {c | baseCarrier c} (mixedSorts (n + n) (l + l')) W)
    (hA : Invariant m (Fin.append b b) (mixedSet W)) (hQ : Covers m Q (mixedSet W)) :
    (rawRVSpace (M := Carrier) (Kt b l)).RelationDefinable (rawRVSpace (M := Carrier) (Kt b l'))
      {c | baseCarrier c} (fun r r' => ∃ p p', joinP p p' ∈ mixedSet W ∧ RI m p ∧ RI m p' ∧
        r = truncOf m b p ∧ r' = truncOf m b p') := by
  refine rawRV_relation_definable_of (tauIdx b) (tauIdx_surjective b)
    (fullTruncSet_definable m (Fin.append b b) Q hW hA hQ) _ fun x y => ?_
  rw [mem_fullTruncSet_iff]
  constructor
  · rintro ⟨p, p', hW', hp, hp', rfl, rfl⟩
    refine ⟨joinP p p', hW', (RI_join m p p').mpr ⟨hp, hp'⟩, ?_⟩
    funext a
    rw [truncOf_join]
  · rintro ⟨q, hq, hRI, hxy⟩
    obtain ⟨p, p', rfl⟩ : ∃ p p', q = joinP p p' := ⟨leftP q, rightP q, (join_left_right q).symm⟩
    obtain ⟨hp, hp'⟩ := (RI_join m p p').mp hRI
    refine ⟨p, p', hq, hp, hp', ?_, ?_⟩
    · funext c
      obtain ⟨a, ha⟩ := tauIdx_surjective b (.inl c)
      have := congrFun hxy a
      rw [truncOf_join, ha] at this
      exact this
    · funext c
      obtain ⟨a, ha⟩ := tauIdx_surjective b (.inr c)
      have := congrFun hxy a
      rw [truncOf_join, ha] at this
      exact this

/-- Label patterns of pairs. -/
def pairPatterns (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ)) : Finset (Fin (l + l') → ℤ) :=
  (Q ×ˢ Q').image (fun qq => Fin.append qq.1 qq.2)

variable {X : Set (Fin (n + l) → Carrier)} {Y : Set (Fin (n + l') → Carrier)}

theorem covers_pairs {Q : Finset (Fin l → ℤ)} {Q' : Finset (Fin l' → ℤ)}
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    {W : Set (Fin ((n + n) + (l + l')) → Carrier)}
    (hW : ∀ p p', joinP p p' ∈ mixedSet W → RI m p → RI m p' → p ∈ mixedSet X ∧ p' ∈ mixedSet Y) :
    Covers m (pairPatterns Q Q') (mixedSet W) := by
  intro q hq hr hu
  obtain ⟨p, p', rfl⟩ : ∃ p p', q = joinP p p' := ⟨leftP q, rightP q, (join_left_right q).symm⟩
  obtain ⟨hp, hp'⟩ := (RI_join m p p').mp ⟨hr, hu⟩
  obtain ⟨hX, hY⟩ := hW p p' hq hp hp'
  obtain ⟨q1, hq1, h1⟩ := hQ p hX hp.1 hp.2
  obtain ⟨q2, hq2, h2⟩ := hQ' p' hY hp'.1 hp'.2
  refine ⟨Fin.append q1 q2, Finset.mem_image.mpr ⟨(q1, q2), Finset.mem_product.mpr ⟨hq1, hq2⟩, rfl⟩, ?_⟩
  intro j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · simp only [joinP, Fin.append_left]
    exact h1 a
  · simp only [joinP, Fin.append_right]
    exact h2 a

/-- **Invariance of truncation classes through a thickened graph.** `W` is a set of pairs, definable
over `ℂ((t))` and `(β, β)`-invariant, containing `(p, Φ p)` for the rational integral points of `X`,
and whose rational integral pairs `(p, p')` have `p ∈ X`, `p' ∈ Y` and `p'[m;β] = (Φ p)[m;β]`. -/
theorem fullClass_eq_of_thickened
    (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hY : DefinableOver {c | baseCarrier c} (mixedSorts n l') Y)
    (hA : Invariant m b (mixedSet X)) (hB : Invariant m b (mixedSet Y))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    (Φ : (Fin n → Ser) × (Fin l → RV) → (Fin n → Ser) × (Fin l' → RV))
    (hmaps : ∀ p ∈ mixedSet X, RI m p → Φ p ∈ mixedSet Y ∧ RI m (Φ p))
    (hsurj : ∀ p' ∈ mixedSet Y, RI m p' → ∃ p ∈ mixedSet X, RI m p ∧ Φ p = p')
    (hresp : ∀ p ∈ mixedSet X, ∀ p' ∈ mixedSet X, RI m p → RI m p' →
      (truncOf m b p = truncOf m b p' ↔ truncOf m b (Φ p) = truncOf m b (Φ p')))
    (W : Set (Fin ((n + n) + (l + l')) → Carrier))
    (hW : DefinableOver {c | baseCarrier c} (mixedSorts (n + n) (l + l')) W)
    (hWA : Invariant m (Fin.append b b) (mixedSet W))
    (hW1 : ∀ p p', joinP p p' ∈ mixedSet W → RI m p → RI m p' →
      p ∈ mixedSet X ∧ p' ∈ mixedSet Y ∧ truncOf m b p' = truncOf m b (Φ p))
    (hW2 : ∀ p ∈ mixedSet X, RI m p → joinP p (Φ p) ∈ mixedSet W) :
    fullClass m b Q hX hA hQ = fullClass m b Q' hY hB hQ' := by
  have hWQ := covers_pairs m hQ hQ' (fun p p' h hp hp' => ⟨(hW1 p p' h hp hp').1, (hW1 p p' h hp hp').2.1⟩)
  refine fullClass_eq_of_correspondence m b Q Q' hX hY hA hB hQ hQ' Φ hmaps hsurj hresp
    ((pairTrunc_relation_definable m b _ hW hWA hWQ).congr _ _ fun r r' => ?_)
  constructor
  · rintro ⟨p, p', hW', hp, hp', rfl, rfl⟩
    exact ⟨p, (hW1 p p' hW' hp hp').1, hp, rfl, (hW1 p p' hW' hp hp').2.2⟩
  · rintro ⟨p, hp, hRI, rfl, rfl⟩
    exact ⟨p, Φ p, hW2 p hp hRI, hRI, (hmaps p hp hRI).2, rfl, rfl⟩

end DiamondIntegral.Section8.Truncation
