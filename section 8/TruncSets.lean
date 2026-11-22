import «section 8».TruncObjects
import FubiniTheorems.Decomposition.RationalFrameComparison

/-! Truncations of sets definable over `ℂ((t))` are definable.

Setting: `X` is a set of raw tuples of the concrete model, definable over `ℂ((t))` at the sorts
`n` field slots then `l` RV slots; `A = mixedSet X` is the corresponding set of points
`(x, u) ∈ ℂ{{t}}^n × RV^l`. Cutoffs `β_i = b_i/m` and a label pattern `q` (the `j`-th label on the
residue line `L_{q_j/m}`) are fixed.

* `polyRep m b c`: the polynomial point `(Σ_{k ≤ b_i} c_{i,k} t^{k/m})_i`.
* `truncSet_pattern_eq`: if `A` is `β`-invariant, the part of `A[m;β]` with labels on the lines of the
  pattern is the image, under `c ↦ (rv(c_{i,k} t^{k/m}), rv(c_j t^{q_j/m}))`, of the coefficient set
  `{c | (polyRep c, labels c) ∈ A}`.
* `truncObject`: the coefficient set as a diagonal constructible object (weights `k/m` and
  `q_j/m`), from `coeffObject`.
* `truncation_definable`: **the truncation is a definable RES set over `ℂ((t))`**: there is a
  definable set `D` of RV tuples of the concrete model, over the base, whose points are exactly the
  points of that part of `A[m;β]` (manuscript, before Lemma 8.5; Hrushovski–Loeser §4.2;
  Denef–Loeser, Germs of arcs, Proposition 2.3). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable DiamondIntegral.Section8.NormalForm

local instance truncSetStructure : LRV.Structure Carrier := canonicalInterpret
local instance truncSetModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {n l : ℕ}

/-- The sorts: `n` field slots, then `l` RV slots. -/
def mixedSorts (n l : ℕ) : Fin (n + l) → SortTag := Fin.addCases (fun _ => .vf) (fun _ => .rv)

/-- The raw tuple of a point `(x, u)`. -/
def mixedRaw (p : (Fin n → Ser) × (Fin l → RV)) : Fin (n + l) → Carrier :=
  Fin.append (fun i => Sum.inl (p.1 i)) (fun j => Sum.inr (p.2 j))

/-- The set of points whose raw tuple lies in `X`. -/
def mixedSet (X : Set (Fin (n + l) → Carrier)) : Set ((Fin n → Ser) × (Fin l → RV)) :=
  {p | mixedRaw p ∈ X}

variable (m : ℕ+) (b : Fin n → ℕ) (q : Fin l → ℤ)

/-- The polynomial point `(Σ_{k ≤ b_i} c_{i,k} t^{k/m})_i`. -/
def polyRep (c : Idx b → ℂ) : Fin n → Ser :=
  fun i => ∑ k : Fin (b i + 1), mono m k (c ⟨i, k⟩)

/-- The labels `rv(c_j t^{q_j/m})`. -/
def labelRep (d : Fin l → ℂ) : Fin l → RV := fun j => linePoint (zlev m (q j)) (d j)

theorem coeffRV_eq_linePoint (γ : ℚ) (a : ℂ) : coeffRV γ a = linePoint γ a := rfl

theorem cf_polyRep (c : Idx b → ℂ) (i : Fin n) (γ : ℚ) :
    cf (polyRep m b c i) γ = ∑ k : Fin (b i + 1), if γ = lev m k then c ⟨i, k⟩ else 0 := by
  rw [polyRep, cf_sum]
  exact Finset.sum_congr rfl fun k _ => cf_mono m k _ γ

theorem cf_polyRep_level (c : Idx b → ℂ) (i : Fin n) (k : Fin (b i + 1)) :
    cf (polyRep m b c i) (lev m k) = c ⟨i, k⟩ := by
  rw [cf_polyRep, Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro k' _ hk'
    rw [if_neg]
    intro h
    exact hk' (Fin.ext (lev_injective m h)).symm
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem cf_polyRep_of_not_level (c : Idx b → ℂ) (i : Fin n) (γ : ℚ)
    (hγ : ∀ k : Fin (b i + 1), γ ≠ lev m k) : cf (polyRep m b c i) γ = 0 := by
  rw [cf_polyRep]
  exact Finset.sum_eq_zero fun k _ => if_neg (hγ k)

theorem polyRep_rational (c : Idx b → ℂ) (i : Fin n) : IsRational m (polyRep m b c i) := by
  intro γ hγ
  by_contra hno
  apply hγ
  apply cf_polyRep_of_not_level
  intro k hk
  exact hno ⟨(k : ℕ), by rw [hk, lev]; push_cast; rfl⟩

theorem polyRep_integral (c : Idx b → ℂ) (i : Fin n) : IsIntegral (polyRep m b c i) := by
  intro γ hγ
  apply cf_polyRep_of_not_level
  intro k hk
  rw [hk] at hγ
  exact absurd (lev_nonneg m k) (not_le.mpr hγ)

theorem truncPoint_polyRep (c : Idx b → ℂ) :
    truncPoint m b (polyRep m b c) = fun k => linePoint (lev m k.2) (c k) := by
  funext k
  obtain ⟨i, k⟩ := k
  change coeffRV (lev m k) (cf (polyRep m b c i) (lev m k)) = _
  rw [cf_polyRep_level]
  rfl

/-- A rational integral point is congruent modulo `𝔪_β` to the polynomial point of its
coefficients. -/
theorem congr_polyRep {x : Fin n → Ser} (hx : ∀ i, IsRational m (x i) ∧ IsIntegral (x i)) :
    Congr m b x (polyRep m b (fun k => cf (x k.1) (lev m k.2))) := by
  intro i γ hγ
  by_cases hlev : ∃ k : Fin (b i + 1), γ = lev m k
  · obtain ⟨k, rfl⟩ := hlev
    rw [cf_polyRep_level]
  · push Not at hlev
    rw [cf_polyRep_of_not_level m b _ i γ hlev]
    by_contra hne
    obtain ⟨z, hz⟩ := (hx i).1 γ hne
    have hz0 : 0 ≤ z := by
      by_contra hneg
      push Not at hneg
      have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
      have : γ < 0 := by
        rw [hz]
        exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) hm
      exact hne ((hx i).2 γ this)
    have hγ' : γ = lev m z.toNat := by
      rw [hz, lev]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hz0).symm
    have hle : z.toNat ≤ b i := by
      by_contra hgt
      push Not at hgt
      rw [hγ'] at hγ
      exact absurd hγ (not_le.mpr (lev_lt_lev hgt))
    exact hlev ⟨z.toNat, Nat.lt_succ_of_le hle⟩ hγ'

/-- The frame of a parameter: `rv(c_{i,k} t^{k/m})` and `rv(c_j t^{q_j/m})`. -/
def frameOf (c : Idx b ⊕ Fin l → ℂ) : Idx b ⊕ Fin l → RV :=
  Sum.elim (fun k => linePoint (lev m k.2) (c (.inl k))) (fun j => linePoint (zlev m (q j)) (c (.inr j)))

/-- The coefficient set of `A`. -/
def coeffSet (A : Set ((Fin n → Ser) × (Fin l → RV))) : Set (Idx b ⊕ Fin l → ℂ) :=
  {c | (polyRep m b (fun k => c (.inl k)), labelRep m q (fun j => c (.inr j))) ∈ A}

theorem labelRational_linePoint (z : ℤ) (a : ℂ) : LabelRational m (linePoint (zlev m z) a) := by
  intro u hu
  by_cases h : a = 0
  · rw [h, linePoint_zero] at hu
    exact absurd hu (by simp)
  · have h1 : linePoint (zlev m z) a = some (Multiplicative.ofAdd (zlev m z), Units.mk0 a h) := by
      simp [linePoint, h]
    rw [h1] at hu
    have h2 := Option.some.inj hu
    rw [← h2]
    exact ⟨z, rfl⟩

/-- **The truncation is the frame image of the coefficient set**, on the labels of pattern `q`. -/
theorem truncSet_pattern_eq (A : Set ((Fin n → Ser) × (Fin l → RV))) (hA : Invariant m b A) :
    {w | w ∈ truncSet m b A ∧ ∀ j, w (.inr j) ∈ Line (zlev m (q j))} =
      frameOf m b q '' coeffSet m b q A := by
  ext w
  constructor
  · rintro ⟨⟨p, hp, hr, hu, rfl⟩, hline⟩
    refine ⟨Sum.elim (fun k => cf (p.1 k.1) (lev m k.2)) (fun j => lineCoeff (p.2 j)), ?_, ?_⟩
    · have hlab : labelRep m q (fun j => lineCoeff (p.2 j)) = p.2 := by
        funext j
        exact coeffRV_lineCoeff (hline j)
      change (polyRep m b (fun k => cf (p.1 k.1) (lev m k.2)), labelRep m q (fun j => lineCoeff (p.2 j))) ∈ A
      rw [hlab]
      exact hA p.1 _ p.2 hp (congr_polyRep m b hr)
    · funext a
      cases a with
      | inl k =>
        show linePoint (lev m k.2) (cf (p.1 k.1) (lev m k.2)) = truncPoint m b p.1 k
        exact (coeffRV_eq_linePoint _ _).symm
      | inr j =>
        show linePoint (zlev m (q j)) (lineCoeff (p.2 j)) = p.2 j
        exact coeffRV_lineCoeff (hline j)
  · rintro ⟨c, hc, rfl⟩
    have hline : ∀ j, frameOf m b q c (.inr j) ∈ Line (zlev m (q j)) := by
      intro j
      show coeffRV (zlev m (q j)) (c (.inr j)) ∈ Line (zlev m (q j))
      exact coeffRV_mem_line _ _
    have hrat : ∀ i, IsRational m (polyRep m b (fun k => c (.inl k)) i) ∧
        IsIntegral (polyRep m b (fun k => c (.inl k)) i) := fun i =>
      ⟨polyRep_rational m b (fun k => c (.inl k)) i, polyRep_integral m b (fun k => c (.inl k)) i⟩
    have hlabs : ∀ j, LabelRational m (labelRep m q (fun j => c (.inr j)) j) := fun j =>
      labelRational_linePoint m (q j) (c (.inr j))
    have hmem : frameOf m b q c ∈ truncSet m b A := by
      refine ⟨(polyRep m b (fun k => c (.inl k)), labelRep m q (fun j => c (.inr j))), hc, hrat, hlabs, ?_⟩
      funext a
      cases a with
      | inl k =>
        show linePoint (lev m k.2) (c (.inl k)) = truncPoint m b (polyRep m b fun k => c (.inl k)) k
        rw [truncPoint_polyRep]
      | inr j => rfl
    exact ⟨hmem, hline⟩

/-! ### The standard data and the definability of the truncation -/

/-- The polynomial point of the standard truncation. -/
def stdPoint (b : Fin n → ℕ) : PolyPoint (Idx b ⊕ Fin l) (n + l) where
  len := Fin.addCases (fun i => b i + 1) (fun _ => 0)
  lvl := fun _ k => k
  var := Fin.addCases
    (fun i k => if h : k < b i + 1 then Sum.inl ⟨i, ⟨k, h⟩⟩ else Sum.inl ⟨i, 0⟩) (fun j _ => Sum.inr j)

/-- The label exponents. -/
def stdExp (q : Fin l → ℤ) : Fin (n + l) → ℤ := Fin.addCases (fun _ => 0) q

/-- The label parameters. -/
def stdLab (b : Fin n → ℕ) : Fin (n + l) → Idx b ⊕ Fin l :=
  Fin.addCases (fun i => Sum.inl ⟨i, 0⟩) (fun j => Sum.inr j)

/-- The weights `k/m` and `q_j/m`. -/
def stdWt : Idx b ⊕ Fin l → ℚ := Sum.elim (fun k => lev m k.2) (fun j => zlev m (q j))

theorem std_len (i : Fin (n + l)) (hi : mixedSorts n l i = .rv) : (stdPoint (l := l) b).len i = 0 := by
  revert hi
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro hi
    simp [mixedSorts] at hi
  · intro _
    simp [stdPoint]

theorem std_var (i : Fin (n + l)) (k : ℕ) (hk : k < (stdPoint (l := l) b).len i) :
    stdWt m b q ((stdPoint (l := l) b).var i k) = lev m ((stdPoint (l := l) b).lvl i k) := by
  revert hk
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro hk
    have hk' : k < b i + 1 := by simpa [stdPoint] using hk
    have hk'' : k ≤ b i := Nat.lt_succ_iff.mp hk'
    simp [stdPoint, stdWt, hk'']
  · intro hk
    simp [stdPoint] at hk

theorem std_lab (i : Fin (n + l)) (hi : mixedSorts n l i = .rv) :
    stdWt m b q (stdLab (l := l) b i) = zlev m (stdExp (n := n) q i) := by
  revert hi
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · intro hi
    simp [mixedSorts] at hi
  · intro _
    simp [stdLab, stdWt, stdExp]

/-- The raw point of the standard data is the raw tuple of the polynomial point with its labels. -/
theorem rawPoint_std (c : Idx b ⊕ Fin l → ℂ) :
    rawPoint m (mixedSorts n l) (stdPoint b) (stdExp q) (stdLab b) c =
      mixedRaw (polyRep m b (fun k => c (.inl k)), labelRep m q (fun j => c (.inr j))) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have hs : mixedSorts n l (Fin.castAdd l i) = .vf := by simp [mixedSorts]
    unfold rawPoint
    simp only [hs]
    rw [mixedRaw, Fin.append_left]
    congr 1
    unfold PolyPoint.eval polyRep
    have hlen : (stdPoint (l := l) b).len (Fin.castAdd l i) = b i + 1 := by simp [stdPoint]
    rw [hlen, ← Fin.sum_univ_eq_sum_range (fun k => mono m ((stdPoint (l := l) b).lvl (Fin.castAdd l i) k)
      (c ((stdPoint (l := l) b).var (Fin.castAdd l i) k))) (b i + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k : ℕ) ≤ b i := Nat.lt_succ_iff.mp k.isLt
    simp [stdPoint, hk]
  · have hs : mixedSorts n l (Fin.natAdd n j) = .rv := by simp [mixedSorts]
    unfold rawPoint
    simp only [hs]
    rw [mixedRaw, Fin.append_right]
    simp [stdExp, stdLab, labelRep]

variable {X : Set (Fin (n + l) → Carrier)}

theorem coeffSet_eq (X : Set (Fin (n + l) → Carrier)) :
    coeffSet m b q (mixedSet X) =
      {c | rawPoint m (mixedSorts n l) (stdPoint b) (stdExp q) (stdLab b) c ∈ X} := by
  ext c
  change mixedRaw _ ∈ X ↔ rawPoint m (mixedSorts n l) (stdPoint b) (stdExp q) (stdLab b) c ∈ X
  rw [rawPoint_std]

/-- **The truncation as a diagonal constructible object**: the coefficient set of the part of
`A[m;β]` with labels of pattern `q`, with weights `k/m` on the coefficient of `t^{k/m}` and `q_j/m`
on the `j`-th label. -/
def truncObject (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) {K : ℕ}
    (ε : Idx b ⊕ Fin l ≃ Fin K) : DiagonalConstructible.Object :=
  coeffObject m (mixedSorts n l) hX (stdPoint b) (std_len b) (stdExp q) (stdLab b) (stdWt m b q)
    (std_var m b q) (std_lab m b q) ε

theorem truncObject_domain (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) {K : ℕ}
    (ε : Idx b ⊕ Fin l ≃ Fin K) :
    (truncObject m b q hX ε).domain = {x | x ∘ ε ∈ coeffSet m b q (mixedSet X)} := by
  rw [coeffSet_eq]
  rfl

theorem truncObject_weights (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) {K : ℕ}
    (ε : Idx b ⊕ Fin l ≃ Fin K) : (truncObject m b q hX ε).weights = stdWt m b q ∘ ε.symm := rfl

/-- **Truncations are definable.** Let `X` be definable over `ℂ((t))` in the concrete model, with
`A = mixedSet X` invariant for the cutoffs `β = b/m`. The part of the truncation `A[m;β]` whose
labels lie on the residue lines of the pattern `q` is the set of points of a definable set `D` of RV
tuples, definable over `ℂ((t))`. -/
theorem truncation_definable (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) {K : ℕ} (ε : Idx b ⊕ Fin l ≃ Fin K) :
    ∃ D : DefSet (rawRVSpace (M := Carrier) K) {c | baseCarrier c},
      ∀ r : Fin K → CanonicalRV.RVSort Carrier, r ∈ D.carrier ↔
        (fun a => taggedRVEquiv (r (ε a))) ∈
          {w | w ∈ truncSet m b (mixedSet X) ∧ ∀ j, w (.inr j) ∈ Line (zlev m (q j))} := by
  have hdef : (Set.univ : Set ℂ).Definable Language.ring
      {x : Fin K → ℂ | x ∘ ε ∈ coeffSet m b q (mixedSet X)} := by
    rw [coeffSet_eq]
    exact (truncObject m b q hX ε).definable
  have hinv : RationalInvariant (stdWt m b q ∘ ε.symm)
      {x : Fin K → ℂ | x ∘ ε ∈ coeffSet m b q (mixedSet X)} := by
    rw [coeffSet_eq]
    exact (truncObject m b q hX ε).invariant
  refine ⟨rationalDescendedSet (stdWt m b q ∘ ε.symm) _ hdef, fun r =>
    (rationalDescent_mem_image (stdWt m b q ∘ ε.symm) _ hdef hinv r).trans ?_⟩
  rw [truncSet_pattern_eq m b q _ hA]
  have hframe : ∀ x : Fin K → ℂ,
      (fun a => taggedRVEquiv (rationalFrame (stdWt m b q ∘ ε.symm) x (ε a))) = frameOf m b q (x ∘ ε) := by
    intro x
    funext a
    cases a with
    | inl k =>
      show linePoint (stdWt m b q (ε.symm (ε (Sum.inl k)))) (x (ε (Sum.inl k))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    | inr j =>
      show linePoint (stdWt m b q (ε.symm (ε (Sum.inr j)))) (x (ε (Sum.inr j))) = _
      rw [Equiv.symm_apply_apply]
      rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hframe]
    exact ⟨x ∘ ε, hx, rfl⟩
  · rintro ⟨c, hc, he⟩
    have hcomp : (c ∘ ε.symm) ∘ ε = c := by
      funext a
      simp
    refine ⟨c ∘ ε.symm, ?_, ?_⟩
    · show (c ∘ ε.symm) ∘ ε ∈ coeffSet m b q (mixedSet X)
      rw [hcomp]
      exact hc
    · have h1 := hframe (c ∘ ε.symm)
      rw [hcomp, he] at h1
      funext i
      have h2 := congrFun h1 (ε.symm i)
      simp only [Equiv.apply_symm_apply] at h2
      exact taggedRVEquiv.injective h2

end DiamondIntegral.Section8.Truncation
