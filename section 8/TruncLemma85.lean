import «section 8».DiagonalClasses

/-! **Lemma 8.5 for classes.** For a set `A` definable over `ℂ((t))`, invariant for the cutoffs
`β = b/m`, and `β ≤ β'`, the normalized truncation classes agree:
`Θ([A[m;β']]) [𝔸]^{-mΣβ'} = Θ([A[m;β]]) [𝔸]^{-mΣβ}` (`lemma_8_5`).

The coefficient set at `β'` is the coefficient set at `β` times the coefficients of `t^{k/m}`,
`β_i < k/m ≤ β'_i` (`coeffSet_extend`), so the truncation object at `β'` is isomorphic to the
product of the one at `β` with an affine space (`truncObject_extend_iso`), whose class is a power of
`[𝔸]` in `K^μ̂ Var_ℂ / (linear actions)` (`dcClass_affineSpace`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm

local instance lemma85Structure : LRV.Structure Carrier := canonicalInterpret
local instance lemma85Model : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable {n l : ℕ} (m : ℕ+) {b b' : Fin n → ℕ} (h : ∀ i, b i ≤ b' i) (q : Fin l → ℤ)

/-- The restriction of a parameter at `β'` to the indices of `β`. -/
def restrictC (c : Idx b' ⊕ Fin l → ℂ) : Idx b ⊕ Fin l → ℂ :=
  Sum.elim (fun k => c (.inl (restrictIdx h k))) (fun j => c (.inr j))

theorem restrictIdx_val (k : Idx b) : ((restrictIdx h k).2 : ℕ) = k.2 := rfl

theorem congr_polyRep_restrict (c : Idx b' ⊕ Fin l → ℂ) :
    Congr m b (polyRep m b' (fun k => c (.inl k))) (polyRep m b (fun k => restrictC h c (.inl k))) := by
  intro i γ hγ
  by_cases hlev : ∃ k : Fin (b i + 1), γ = lev m k
  · obtain ⟨k, rfl⟩ := hlev
    have hk' : (k : ℕ) < b' i + 1 := lt_of_lt_of_le k.isLt (Nat.succ_le_succ (h i))
    have e1 := cf_polyRep_level m b' (fun k => c (.inl k)) i ⟨k, hk'⟩
    have e2 := cf_polyRep_level m b (fun k => restrictC h c (.inl k)) i k
    simp only [Fin.val_mk] at e1
    rw [e1, e2]
    rfl
  · push Not at hlev
    rw [cf_polyRep_of_not_level m b _ i γ hlev, cf_polyRep_of_not_level m b' _ i γ]
    intro k hk
    have hkb : (k : ℕ) ≤ b i := by
      by_contra hgt
      push Not at hgt
      rw [hk] at hγ
      exact absurd hγ (not_le.mpr (lev_lt_lev hgt))
    exact hlev ⟨k, Nat.lt_succ_of_le hkb⟩ hk

theorem congr_symm {x y : Fin n → Ser} (hxy : Congr m b x y) : Congr m b y x :=
  fun i γ hγ => (hxy i γ hγ).symm

/-- **The coefficient set at `β'`** is the preimage of the coefficient set at `β`. -/
theorem coeffSet_extend (A : Set ((Fin n → Ser) × (Fin l → RV))) (hA : Invariant m b A)
    (c : Idx b' ⊕ Fin l → ℂ) : c ∈ coeffSet m b' q A ↔ restrictC h c ∈ coeffSet m b q A := by
  have hc := congr_polyRep_restrict m h c
  constructor
  · intro hc'
    exact hA _ _ _ hc' hc
  · intro hc'
    exact hA _ _ _ hc' (congr_symm m hc)

/-- The extra indices `β_i < k/m ≤ β'_i`. -/
abbrev Extra (b b' : Fin n → ℕ) := {k : Idx b' // b k.1 < (k.2 : ℕ)}

/-- The indices of `β` inside those of `β'`. -/
def lowEquiv : Idx b ≃ {k : Idx b' // ¬ b k.1 < (k.2 : ℕ)} where
  toFun k := ⟨restrictIdx h k, by simp only [restrictIdx_val]; exact not_lt.mpr (Nat.lt_succ_iff.mp k.2.isLt)⟩
  invFun k := ⟨k.1.1, ⟨k.1.2, Nat.lt_succ_of_le (not_lt.mp k.2)⟩⟩
  left_inv k := rfl
  right_inv k := rfl

/-- `Idx β' ⊕ labels ≃ (Idx β ⊕ labels) ⊕ extra`. -/
def splitEquiv : Idx b' ⊕ Fin l ≃ (Idx b ⊕ Fin l) ⊕ Extra b b' :=
  (Equiv.sumCongr ((Equiv.sumCompl (fun k : Idx b' => b k.1 < (k.2 : ℕ))).symm.trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCongr (lowEquiv h).symm (Equiv.refl _))))
    (Equiv.refl (Fin l))).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      (Equiv.sumAssoc _ _ _).symm))

theorem splitEquiv_symm_low (k : Idx b) :
    (splitEquiv (l := l) h).symm (.inl (.inl k)) = .inl (restrictIdx h k) := rfl

theorem splitEquiv_symm_label (j : Fin l) : (splitEquiv (b := b) (b' := b') h).symm (.inl (.inr j)) = .inr j := rfl

theorem splitEquiv_symm_extra (k : Extra b b') : (splitEquiv (l := l) h).symm (.inr k) = .inl k.1 := rfl

/-- The weights of the extra coordinates. -/
def extraWt (εE : Extra b b' ≃ Fin (Fintype.card (Extra b b'))) : Fin (Fintype.card (Extra b b')) → ℚ :=
  fun e => lev m (εE.symm e).1.2

include h in
theorem card_extend :
    Fintype.card (Idx b' ⊕ Fin l) = Fintype.card (Idx b ⊕ Fin l) + Fintype.card (Extra b b') := by
  rw [Fintype.card_congr (splitEquiv (l := l) h), Fintype.card_sum]

variable {X : Set (Fin (n + l) → Carrier)}

/-- **The truncation object at `β'` is the one at `β` times an affine space.** -/
def truncObject_extend_iso (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) :
    DiagonalConstructible.Iso (truncObject m b' q hX (Fintype.equivFin _))
      (DiagonalConstructible.product (truncObject m b q hX (Fintype.equivFin _))
        (DiagonalConstructible.affineSpace (extraWt m (Fintype.equivFin (Extra b b'))))) := by
  let ε' := Fintype.equivFin (Idx b' ⊕ Fin l)
  let ε := Fintype.equivFin (Idx b ⊕ Fin l)
  let εE := Fintype.equivFin (Extra b b')
  let π : Fin (Fintype.card (Idx b' ⊕ Fin l)) ≃ Fin (Fintype.card (Idx b ⊕ Fin l) + Fintype.card (Extra b b')) :=
    ε'.symm.trans ((splitEquiv h).trans ((Equiv.sumCongr ε εE).trans finSumFinEquiv))
  have hπ : ∀ a, π.symm (Fin.castAdd _ (ε a)) = ε' ((splitEquiv h).symm (.inl a)) := by
    intro a
    simp only [π, Equiv.symm_trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, Equiv.symm_symm]
  refine reindexIso _ _ π ?_ ?_
  · intro i
    obtain ⟨a, rfl⟩ := ε'.surjective i
    change (Fin.append (stdWt m b q ∘ ε.symm) (extraWt m εE))
        (finSumFinEquiv (Equiv.sumCongr ε εE (splitEquiv h (ε'.symm (ε' a))))) = stdWt m b' q (ε'.symm (ε' a))
    rw [Equiv.symm_apply_apply]
    have ha : a = (splitEquiv h).symm (splitEquiv h a) := (Equiv.symm_apply_apply _ _).symm
    rcases hs : splitEquiv h a with (k | j) | e
    · rw [hs] at ha
      rw [ha, splitEquiv_symm_low]
      simp only [Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.append_left,
        Function.comp_apply, Equiv.symm_apply_apply, stdWt, Sum.elim_inl]
      rfl
    · rw [hs] at ha
      rw [ha, splitEquiv_symm_label]
      simp only [Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.append_left,
        Function.comp_apply, Equiv.symm_apply_apply, stdWt, Sum.elim_inr]
    · rw [hs] at ha
      rw [ha, splitEquiv_symm_extra]
      simp only [Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, Fin.append_right,
        extraWt, stdWt, Sum.elim_inl]
      rw [Equiv.symm_apply_apply]
  · intro x
    rw [truncObject_domain]
    change x ∘ ε' ∈ coeffSet m b' q (mixedSet X) ↔
      (fun i => (x ∘ π.symm) (Fin.castAdd _ i)) ∈ (truncObject m b q hX ε).domain ∧ True
    rw [truncObject_domain, and_true, coeffSet_extend m h q _ hA]
    simp only [Set.mem_ofPred_eq]
    have he : (fun i => (x ∘ π.symm) (Fin.castAdd _ i)) ∘ ε = restrictC h (x ∘ ε') := by
      funext a
      simp only [Function.comp_apply, hπ]
      cases a with
      | inl k => rfl
      | inr j => rfl
    rw [he]

theorem card_idx (b : Fin n → ℕ) : Fintype.card (Idx b ⊕ Fin l) = (∑ i, b i) + n + l := by
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp [Finset.sum_add_distrib]

include h in
/-- **Lemma 8.5 for classes.** -/
theorem lemma_8_5 (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) : truncClass m b' q hX = truncClass m b q hX := by
  have hcard : (∑ i, b' i) = (∑ i, b i) + Fintype.card (Extra b b') := by
    have h1 := card_extend (l := l) h
    rw [card_idx, card_idx] at h1
    omega
  rw [truncClass, truncClass, dcClass_iso (truncObject_extend_iso m h q hX hA), dcClass_product,
    dcClass_affineSpace, map_mul, map_pow, hcard, Linv, Linv, pow_add, ← Lunit_val]
  have hu : (Lunit : Rloc) * ((Lunit⁻¹ : Rlocˣ) : Rloc) = 1 := Units.mul_inv Lunit
  calc _ = algebraMap EquivariantVariety.ModifiedRing Rloc
        (dcClass (truncObject m b q hX (Fintype.equivFin _))) * ((Lunit⁻¹ : Rlocˣ) : Rloc) ^ (∑ i, b i) *
          ((Lunit : Rloc) * ((Lunit⁻¹ : Rlocˣ) : Rloc)) ^ Fintype.card (Extra b b') := by ring
    _ = _ := by rw [hu, one_pow, mul_one]

end DiamondIntegral.Section8.Truncation
