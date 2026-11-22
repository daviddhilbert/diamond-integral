import «section 8».TruncCoefficients
import «section 8».RingDefinable
import FubiniTheorems.Decomposition.FiniteFrameComparison
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxConcreteModel

/-! Constructibility of conditions on leading terms.

* `IsPiecewise m lam`: a function `lam : (σ → ℂ) → RV` that, on each piece of a finite constructible
  cover of `ℂ^σ`, is `c ↦ rv(G(c) t^{e/m})` for a polynomial `G` and an integer `e`.
* `isPiecewise_fam`: `c ↦ rv(y c)` is piecewise in this sense for a family `y` with polynomial
  coefficients (the pieces say which coefficient is the first nonzero one; there are finitely many
  by `exists_bound`).
* `rdef_piecewise`: for piecewise `lam_1, …, lam_k` and a definable RV set `Ψ` of the concrete
  model, `{c | (lam_j c)_j ∈ Ψ}` is constructible. On each piece this is the preimage under a
  polynomial map of the library's framed set of `Ψ` (`framedRVSet_pure_definable`). -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable

local instance truncSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance truncSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {σ : Type}

/-- Piecewise `c ↦ rv(G(c) t^{e/m})` on a finite constructible cover. -/
def IsPiecewise (m : ℕ+) (lam : (σ → ℂ) → RV) : Prop :=
  ∃ (n : ℕ) (D : Fin n → Set (σ → ℂ)) (e : Fin n → ℤ) (G : Fin n → MvPolynomial σ ℂ),
    (∀ a, RDef (D a)) ∧ (∀ c, ∃ a, c ∈ D a) ∧
      ∀ a, ∀ c ∈ D a, lam c = linePoint (zlev m (e a)) (MvPolynomial.eval c (G a))

theorem linePoint_zero (q : ℚ) : linePoint q 0 = none := by simp [linePoint]

theorem isPiecewise_label (m : ℕ+) (e : ℤ) (s : σ) :
    IsPiecewise m (fun c => linePoint (zlev m e) (c s)) :=
  ⟨1, fun _ => Set.univ, fun _ => e, fun _ => MvPolynomial.X s, fun _ => rdef_univ,
    fun _ => ⟨0, trivial⟩, fun _ c _ => by rw [MvPolynomial.eval_X]⟩

theorem isPiecewise_none (m : ℕ+) : IsPiecewise m (fun _ : σ → ℂ => (none : RV)) :=
  ⟨1, fun _ => Set.univ, fun _ => 0, fun _ => 0, fun _ => rdef_univ,
    fun _ => ⟨0, trivial⟩, fun _ c _ => by rw [map_zero, linePoint_zero]⟩

theorem isPiecewise_fam [Finite σ] {m : ℕ+} {y : (σ → ℂ) → Ser} (hy : IsFam m y) :
    IsPiecewise m (fun c => rvOfField (y c)) := by
  obtain ⟨r₀, Q, hQ, h⟩ := hy
  obtain ⟨R, hR⟩ := exists_bound Q
  let L : ℕ := (R - r₀ + 1).toNat
  have hidx : ∀ r : ℤ, r₀ ≤ r → r ≤ R → ((r - r₀).toNat < L ∧ r₀ + ((r - r₀).toNat : ℤ) = r) := by
    intro r h1 h2
    constructor
    · change (r - r₀).toNat < (R - r₀ + 1).toNat
      omega
    · omega
  refine ⟨L + 1,
    fun a => {c | ((a : ℕ) < L → MvPolynomial.eval c (Q (r₀ + (a : ℕ))) ≠ 0)} ∩
      ⋂ a' : Fin L, {c | (a' : ℕ) < (a : ℕ) → MvPolynomial.eval c (Q (r₀ + (a' : ℕ))) = 0},
    fun a => r₀ + (a : ℕ),
    fun a => if (a : ℕ) < L then Q (r₀ + (a : ℕ)) else 0, ?_, ?_, ?_⟩
  · intro a
    refine Set.Definable.inter ?_ (rdef_iInter fun a' => ?_)
    · by_cases ha : (a : ℕ) < L
      · convert rdef_ne (Q (r₀ + (a : ℕ))) using 1
        ext c
        simp only [Set.mem_ofPred_eq, ha, forall_true_left]
      · convert rdef_univ (α := σ) using 1
        ext c
        simp only [Set.mem_ofPred_eq, ha, IsEmpty.forall_iff, Set.mem_univ]
    · by_cases ha : (a' : ℕ) < (a : ℕ)
      · convert rdef_zero (Q (r₀ + (a' : ℕ))) using 1
        ext c
        simp only [Set.mem_ofPred_eq, ha, forall_true_left]
      · convert rdef_univ (α := σ) using 1
        ext c
        simp only [Set.mem_ofPred_eq, ha, IsEmpty.forall_iff, Set.mem_univ]
  · intro c
    by_cases hex : ∃ k : ℕ, k < L ∧ MvPolynomial.eval c (Q (r₀ + (k : ℤ))) ≠ 0
    · have hk := Nat.find_spec hex
      refine ⟨⟨Nat.find hex, Nat.lt_succ_of_lt hk.1⟩, ?_, ?_⟩
      · intro _
        exact hk.2
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        intro a' ha'
        by_contra hne
        exact Nat.find_min hex ha' ⟨a'.isLt, hne⟩
    · push Not at hex
      refine ⟨Fin.last L, ?_, ?_⟩
      · intro hlt
        exact absurd hlt (lt_irrefl _)
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        intro a' _
        exact hex a' a'.isLt
  · rintro a c ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h1 h2
    by_cases ha : (a : ℕ) < L
    · simp only [ha, if_true]
      have hne : cf (y c) (zlev m (r₀ + (a : ℕ))) ≠ 0 := by
        rw [(h c).2]; exact h1 ha
      have hlow : ∀ r' : ℤ, r' < r₀ + (a : ℕ) → cf (y c) (zlev m r') = 0 := by
        intro r' hr'
        rw [(h c).2 r']
        by_cases hlt : r' < r₀
        · rw [hQ r' hlt, map_zero]
        · have hk : (r' - r₀).toNat < (a : ℕ) := by omega
          have := h2 ⟨(r' - r₀).toNat, lt_trans hk ha⟩ hk
          have he : r₀ + (((r' - r₀).toNat : ℕ) : ℤ) = r' := by omega
          rwa [he] at this
      rw [rvOfField_eq_linePoint (h c).1 _ hne hlow, (h c).2]
    · simp only [ha, if_false, map_zero, linePoint_zero]
      have haL : (a : ℕ) = L := by have := a.isLt; omega
      have hall : ∀ r, r ≤ R → MvPolynomial.eval c (Q r) = 0 := by
        intro r hr
        by_cases hlt : r < r₀
        · rw [hQ r hlt, map_zero]
        · obtain ⟨hk, he⟩ := hidx r (not_lt.mp hlt) hr
          have := h2 ⟨(r - r₀).toNat, hk⟩ (by rw [haL]; exact hk)
          rwa [he] at this
      have hzero : y c = 0 := eq_zero_of_cf (h c).1 (fun r => by rw [(h c).2 r]; exact hR c hall r)
      rw [hzero, rvOfField_zero']

/-- **Conditions on leading terms are constructible.** -/
theorem rdef_piecewise [Finite σ] (m : ℕ+) {k : ℕ} (lam : Fin k → (σ → ℂ) → RV)
    (h : ∀ j, IsPiecewise m (lam j)) {S' : Set Carrier}
    (Ψ : DefSet (rawRVSpace (M := Carrier) k) S') :
    RDef {c : σ → ℂ | (fun j => rvTag (lam j c)) ∈ Ψ.carrier} := by
  choose n D e G hD hcov hval using h
  have hpiece : ∀ a : (∀ j, Fin (n j)), RDef ((⋂ j, D j (a j)) ∩
      {c | (fun j => MvPolynomial.eval c (G j (a j))) ∈ framedRVSet m (fun j => e j (a j)) Ψ}) :=
    fun a => (rdef_iInter fun j => hD j (a j)).inter
      (rdef_preimage_poly _ _ (framedRVSet_pure_definable m _ Ψ))
  convert rdef_iUnion hpiece using 1
  ext c
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  have key : ∀ a : (∀ j, Fin (n j)), (∀ j, c ∈ D j (a j)) →
      ((fun j => rvTag (lam j c)) ∈ Ψ.carrier ↔
        (fun j => MvPolynomial.eval c (G j (a j))) ∈ framedRVSet m (fun j => e j (a j)) Ψ) := by
    intro a ha
    have he : (fun j => rvTag (lam j c)) = fun j => rvTag (finiteFrame m (fun j => e j (a j))
        (fun j => MvPolynomial.eval c (G j (a j))) j) := by
      funext j
      rw [hval j (a j) c (ha j)]
      rfl
    rw [he]
    rfl
  constructor
  · intro hc
    choose a ha using fun j => hcov j c
    exact ⟨a, ha, (key a ha).mp hc⟩
  · rintro ⟨a, ha, hc⟩
    exact (key a ha).mpr hc

end DiamondIntegral.Section8.Truncation
