import «section 8».TruncDefinable
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxDefinableMaps
import FubiniTheorems.Decomposition.DiagonalConstructibleRing

/-! Coefficient sets of sets definable over `ℂ((t))` are constructible sets with a diagonal
action of the compatible roots of unity.

* `base_rational`: the field-sort elements of the base `ℂ((t))` are `m`-rational for every `m`.
* `rawPoint_action`: the Galois action of a compatible root system `η` on a raw point is the raw
  point of the twisted parameter `c_s ↦ χ_η(wt s) c_s`, when each parameter `s` is used at the
  level `wt s`.
* `coefficient_invariant`: the coefficient set of a set definable over `ℂ((t))` is invariant under
  the twist.
* `coeffObject`: the coefficient set as a diagonal constructible object (the library's
  `DiagonalConstructible.Object`: a constructible subset of `ℂ^K` with rational weights, invariant
  under the weighted action). Its class in `K^μ̂ Var_ℂ` is given by the library's
  `DiagonalConstructible.toVarietyRing`. -/

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

local instance truncObjStructure : LRV.Structure Carrier := canonicalInterpret
local instance truncObjModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {σ : Type} {N : ℕ}

/-- The field-sort elements of the base `ℂ((t))` are `m`-rational. -/
theorem base_rational (m : ℕ+) (f : Ser) (hf : baseCarrier (Sum.inl f : Carrier)) : IsRational m f := by
  obtain ⟨g, hg⟩ := hf
  intro γ hγ
  have hmem : ((f : Ser) : HahnSeries ℚ ℂ) ∈ Set.range (laurentToRational (k := ℂ) (n := 1) (by omega)) :=
    ⟨g, by rw [← hg]; rfl⟩
  obtain ⟨z, hz⟩ := (laurentToRational_range_iff (n := 1) (by omega) _).mp hmem hγ
  have hz' : (z : ℚ) = γ := by simpa [rationalExponentMap] using hz
  refine ⟨z * (m : ℕ), ?_⟩
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  rw [← hz']
  push_cast
  field_simp

/-- The twist of a parameter by the character of `η` at the weights `wt`. -/
def twist (wt : σ → ℚ) (η : CompatibleRoots ℂ) (c : σ → ℂ) : σ → ℂ :=
  fun s => ((compatibleRootCharacter η (Multiplicative.ofAdd (wt s)) : ℂˣ) : ℂ) * c s

theorem cf_action (η : CompatibleRoots ℂ) (f : Ser) (γ : ℚ) :
    cf (puiseuxRootSystemAction η f) γ =
      ((compatibleRootCharacter η (Multiplicative.ofAdd γ) : ℂˣ) : ℂ) * cf f γ := rfl

theorem action_mono (η : CompatibleRoots ℂ) (m : ℕ+) (j : ℕ) (a : ℂ) :
    puiseuxRootSystemAction η (mono m j a) =
      mono m j (((compatibleRootCharacter η (Multiplicative.ofAdd (lev m j)) : ℂˣ) : ℂ) * a) := by
  apply Subtype.ext
  ext γ
  change cf (puiseuxRootSystemAction η (mono m j a)) γ = cf (mono m j _) γ
  rw [cf_action, cf_mono, cf_mono]
  by_cases h : γ = lev m j
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The Galois action on a raw point is the raw point of the twisted parameter. -/
theorem rawPoint_action (m : ℕ+) (sn : Fin N → SortTag) (p : PolyPoint σ N) (e : Fin N → ℤ)
    (lab : Fin N → σ) (wt : σ → ℚ) (hvar : ∀ i k, k < p.len i → wt (p.var i k) = lev m (p.lvl i k))
    (hlab : ∀ i, sn i = .rv → wt (lab i) = zlev m (e i)) (η : CompatibleRoots ℂ) (c : σ → ℂ) :
    carrierAction η ∘ rawPoint m sn p e lab c = rawPoint m sn p e lab (twist wt η c) := by
  funext i
  simp only [Function.comp]
  unfold rawPoint
  cases hi : sn i with
  | vf =>
    simp only
    rw [carrierAction_inl]
    congr 1
    unfold PolyPoint.eval
    rw [map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [action_mono, twist, hvar i k (Finset.mem_range.mp hk)]
  | rv =>
    simp only
    rw [carrierAction_inr, rvAction_linePoint, twist, hlab i hi]

/-- The coefficient set of a set definable over `ℂ((t))` is invariant under the twist. -/
theorem coefficient_invariant (m : ℕ+) (sn : Fin N → SortTag) {X : Set (Fin N → Carrier)}
    (hX : {c | baseCarrier c}.Definable LRV X) (p : PolyPoint σ N) (e : Fin N → ℤ)
    (lab : Fin N → σ) (wt : σ → ℚ) (hvar : ∀ i k, k < p.len i → wt (p.var i k) = lev m (p.lvl i k))
    (hlab : ∀ i, sn i = .rv → wt (lab i) = zlev m (e i)) (η : CompatibleRoots ℂ) (c : σ → ℂ) :
    rawPoint m sn p e lab (twist wt η c) ∈ X ↔ rawPoint m sn p e lab c ∈ X := by
  rw [← rawPoint_action m sn p e lab wt hvar hlab η c]
  exact raw_original_definable_invariant η X hX _

theorem base_definable_of_definableOver (sn : Fin N → SortTag) {X : Set (Fin N → Carrier)}
    (hX : DefinableOver {c | baseCarrier c} sn X) : {c | baseCarrier c}.Definable LRV X := by
  obtain ⟨hraw, -⟩ := (definableOver_iff_normalized_raw _ sn X).mp hX
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hraw
  exact hraw

/-- **The coefficient set as a diagonal constructible object.** For `X` definable over `ℂ((t))`, a
polynomial point `p` and labels, with each parameter used at the level `wt`, and an enumeration `ε`
of the parameters. -/
def coeffObject (m : ℕ+) (sn : Fin N → SortTag) {X : Set (Fin N → Carrier)}
    (hX : DefinableOver {c | baseCarrier c} sn X) (p : PolyPoint σ N)
    (hp : ∀ i, sn i = .rv → p.len i = 0) (e : Fin N → ℤ) (lab : Fin N → σ) (wt : σ → ℚ)
    (hvar : ∀ i k, k < p.len i → wt (p.var i k) = lev m (p.lvl i k))
    (hlab : ∀ i, sn i = .rv → wt (lab i) = zlev m (e i)) {K : ℕ} (ε : σ ≃ Fin K) :
    DiagonalConstructible.Object where
  arity := K
  weights := wt ∘ ε.symm
  domain := {x | rawPoint m sn p e lab (x ∘ ε) ∈ X}
  definable := by
    have : Finite σ := Finite.of_equiv _ ε.symm
    have h := coefficient_constructible m sn (fun f hf => base_rational m f hf) hX p hp e lab
    have h' := h.preimage_comp (ε : σ → Fin K)
    exact h'
  invariant := by
    intro η x
    have h := coefficient_invariant m sn (base_definable_of_definableOver sn hX) p e lab wt hvar hlab η
      (x ∘ ε)
    have he : rationalAction (wt ∘ ε.symm) η x ∘ ε = twist wt η (x ∘ ε) := by
      funext s
      simp only [Function.comp, rationalAction, twist, Equiv.symm_apply_apply]
    change rawPoint m sn p e lab (rationalAction (wt ∘ ε.symm) η x ∘ ε) ∈ X ↔ _
    rw [he]
    exact h

end DiamondIntegral.Section8.Truncation
